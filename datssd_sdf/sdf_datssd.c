/* ====================================================================
 * Copyright (c) 2014 - 2017 The GmSSL Project.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * 3. All advertising materials mentioning features or use of this
 *    software must display the following acknowledgment:
 *    "This product includes software developed by the GmSSL Project.
 *    (http://gmssl.org/)"
 *
 * 4. The name "GmSSL Project" must not be used to endorse or promote
 *    products derived from this software without prior written
 *    permission. For written permission, please contact
 *    guanzhi1980@gmail.com.
 *
 * 5. Products derived from this software may not be called "GmSSL"
 *    nor may "GmSSL" appear in their names without prior written
 *    permission of the GmSSL Project.
 *
 * 6. Redistributions of any form whatsoever must retain the following
 *    acknowledgment:
 *    "This product includes software developed by the GmSSL Project
 *    (http://gmssl.org/)"
 *
 * THIS SOFTWARE IS PROVIDED BY THE GmSSL PROJECT ``AS IS'' AND ANY
 * EXPRESSED OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE GmSSL PROJECT OR
 * ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 * ====================================================================
 */

#include <malloc.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <arpa/inet.h>
#include <scsi/sg.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <linux/hdreg.h>
#include <errno.h>
#include <sys/types.h>
#include <dirent.h>
#include <fnmatch.h>
#include <linux/version.h>
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4, 4, 0)
#include <linux/nvme_ioctl.h>
#else
#include <linux/nvme.h>
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <openssl/sgd.h>
#include <openssl/sdf.h>
#include <openssl/engine.h>
#include <openssl/sms4.h>

typedef int DeviceHandle;

#define DEVICE_SATA (0)
#define DEVICE_NVME (1)

#define SUPPORT_PRINTF 1

#define SUPPORT_FUCTION 0


#if (SUPPORT_PRINTF)
#define SDF_TRACE() fprintf(stderr, "DATSSD->%s\n", __FUNCTION__)
#define DRIVER_TRACE() fprintf(stderr, "Driver->%s\n", __FUNCTION__)
#define debug_hex_print(msg,str,len) do{vdebug_hex_print(msg,str,len); }while(0)
#else
#define SDF_TRACE() 
#define DRIVER_TRACE()
#define debug_hex_print(msg,str,len) 
#endif
#define MODULENAME_LEN 40

#define TRANSFER_LEN   4096

#define  NVME_SECURITY_SEND 0x81
#define  NVME_SECURITY_RECV 0x82
#define  NVME_IDENTIFY 0x06

static char *sdf_deviceHandle;
static char *sessionHandle;
static char *keyHandle = "SDF Key Handle";
static char *agreementHandle = "SDF Agreement Handle";
static DeviceHandle sDeviceHandle;
static uint8_t isOpen = FALSE;
static uint8_t device_type;
static uint8_t hash_type;

static uint8_t s_SDF_SendBuf[TRANSFER_LEN];
static uint8_t s_SDF_RevBuf[TRANSFER_LEN];
//APDU CLA
#define cla_securify	  0x80
//APDU INS
#define ins_device_info   0x04
#define ins_get_random    0x50
//文件操作
#define ins_create_dir    0x30
#define ins_delete_dir    0x32
#define ins_create_ef 	  0x34
#define ins_delete_ef  	  0x36
#define ins_read_ef  	  0x38
#define ins_write_ef  	  0x3a
#define ins_enu_file_info 0x3c
#define ins_select_file   0x3e
//非对称密钥操作
#define ins_asy_gen  	  0x54
#define ins_asy_import    0x58
#define ins_asy_export    0x5c
#define ins_asy_destory   0x60
#define ins_asy_enc  	  0xa2
#define ins_asy_dec 	  0xa4
#define ins_asy_sign  	  0xa6
#define ins_asy_verify    0xa8
//对称密钥操作  
#define ins_sy_gen  	  0x56
#define ins_sy_import     0x5a
#define ins_sy_export     0x5e
#define ins_sy_destory    0x62
#define ins_sy_operate    0xa0
#define ins_backup_key    0x64
#define ins_restore_key   0x66
//hash  
#define ins_hash  		  0xaa
#define ins_hmac  		  0xac
//pin  
#define ins_pin_get  	  0x12
#define ins_pin_verify    0x14
#define ins_pin_change    0x16
#define ins_pin_logout    0x18
//用户操作
#define ins_person_active_add   0x40
#define ins_person_change_name  0x42
//session
#define ins_session_start  		0x82
#define ins_session_gen 		0x84

#define CLA      	 s_SDF_SendBuf[0]   
#define INS      	 s_SDF_SendBuf[1]   
#define P1      	 s_SDF_SendBuf[2]   
#define P2      	 s_SDF_SendBuf[3]   
#define P3      	 s_SDF_SendBuf[4]   
#define DATA_BUF     (s_SDF_SendBuf + 5)

#define ECC_BIT_LEN	256



unsigned char rsaPublicKeyBuf[516] = {
	0x00,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0xd5,0x43,0xbf,0x24,0xd2,0x69,0x56,0x21,0x20,0x57,0x8a,0xd8,
	0x67,0x4f,0xbd,0xd5,0xf5,0x3a,0xf5,0x9e,0xa5,0x87,0x52,0x39,0x47,0xc3,0xce,0x32,
	0x56,0xb6,0x06,0x2d,0xdc,0x8d,0xc2,0x18,0x53,0x5c,0xb0,0xcb,0xb6,0xe8,0x7c,0x82,
	0x97,0x38,0xbb,0x85,0x45,0x2e,0xc8,0x24,0x08,0x96,0x9e,0xb0,0x00,0xaf,0xd9,0xa7,
	0x1f,0x50,0x7f,0xc4,0x93,0x14,0x74,0x9a,0x43,0x8e,0x04,0x95,0xa0,0xd6,0xd9,0xdd,
	0xb4,0x97,0xb3,0x52,0x93,0xe4,0xbe,0xd1,0x1f,0x8c,0xf9,0xcd,0xe1,0xae,0x54,0xae,
	0x72,0xdf,0x94,0xe3,0x15,0x6a,0x5c,0x99,0xd6,0x80,0x46,0x94,0xad,0xb3,0x76,0x95,
	0x4e,0x14,0x8f,0x8f,0xe5,0x55,0xf1,0x3f,0xd0,0xd3,0x96,0x01,0xf6,0x94,0x3e,0x61,
	0xc1,0x8e,0xb3,0x89,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x01,0x00,0x01,};
unsigned char rsaPrivateKeyBuf[1412] = {
	0x00,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0xd5,0x43,0xbf,0x24,0xd2,0x69,0x56,0x21,0x20,0x57,0x8a,0xd8,
	0x67,0x4f,0xbd,0xd5,0xf5,0x3a,0xf5,0x9e,0xa5,0x87,0x52,0x39,0x47,0xc3,0xce,0x32,
	0x56,0xb6,0x06,0x2d,0xdc,0x8d,0xc2,0x18,0x53,0x5c,0xb0,0xcb,0xb6,0xe8,0x7c,0x82,
	0x97,0x38,0xbb,0x85,0x45,0x2e,0xc8,0x24,0x08,0x96,0x9e,0xb0,0x00,0xaf,0xd9,0xa7,
	0x1f,0x50,0x7f,0xc4,0x93,0x14,0x74,0x9a,0x43,0x8e,0x04,0x95,0xa0,0xd6,0xd9,0xdd,
	0xb4,0x97,0xb3,0x52,0x93,0xe4,0xbe,0xd1,0x1f,0x8c,0xf9,0xcd,0xe1,0xae,0x54,0xae,
	0x72,0xdf,0x94,0xe3,0x15,0x6a,0x5c,0x99,0xd6,0x80,0x46,0x94,0xad,0xb3,0x76,0x95,
	0x4e,0x14,0x8f,0x8f,0xe5,0x55,0xf1,0x3f,0xd0,0xd3,0x96,0x01,0xf6,0x94,0x3e,0x61,
	0xc1,0x8e,0xb3,0x89,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x01,0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x1e,0xd9,0x55,0xe4,0xf5,0xaa,0xd7,0x12,0xa3,0xa3,0x06,0x2a,
	0x97,0x87,0x29,0x66,0xb1,0xba,0x7d,0x9d,0x1d,0x44,0x9d,0xd8,0x3b,0x51,0x4f,0x9a,
	0x68,0x80,0x9c,0x14,0x36,0x3b,0x2b,0x40,0x69,0x8e,0x96,0xe4,0x60,0xe8,0xf0,0x59,
	0xd3,0x96,0x19,0x4a,0x05,0xdf,0xe6,0x83,0x8f,0xda,0x79,0xc9,0xeb,0xcf,0x84,0x24,
	0x70,0x9b,0x2c,0x5f,0xf7,0x56,0xe2,0xe0,0xc7,0xfb,0x67,0x92,0xd2,0xf6,0x59,0x19,
	0xe9,0xdd,0xb4,0x54,0x52,0x0d,0xf8,0xda,0x64,0x67,0xe0,0xb9,0xe6,0x52,0x08,0xff,
	0x28,0x06,0x89,0x5c,0x2b,0xd5,0x6e,0x21,0xe1,0x6d,0x1d,0xe3,0xf8,0x1e,0x0f,0x20,
	0x9f,0x0a,0x60,0xd1,0xff,0x4e,0xa2,0x45,0xa1,0xee,0x96,0x90,0xc0,0xc4,0xa8,0x25,
	0x5a,0xe8,0xe8,0xa1,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0xf5,0xde,0x0d,0x0c,0xc5,0x03,0x53,0x44,0xfa,0x70,0xc7,0x44,
	0x63,0xf8,0x57,0x7e,0x49,0x76,0xe4,0x7a,0x76,0x01,0x7d,0xda,0x65,0xaa,0x9d,0xbe,
	0xfe,0x24,0x9b,0x48,0xf9,0xa8,0x18,0x42,0x47,0xf3,0x1a,0x1e,0x61,0xe9,0xb8,0xb3,
	0x07,0xee,0xfd,0x83,0x2e,0xf2,0xf8,0xb9,0x1f,0x9a,0xee,0xeb,0x21,0xd0,0xc0,0x13,
	0xa2,0x31,0x33,0xe7,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0xde,0x0d,0xba,0xf3,0x62,0x8f,0x75,0x16,0xe6,0x87,0x72,0xba,
	0x12,0x6a,0x43,0x5c,0xde,0x22,0x60,0xea,0xef,0x7a,0x7e,0xb6,0x28,0x16,0x4f,0xda,
	0xe7,0xb8,0xfe,0x48,0x17,0x65,0x1a,0x73,0x38,0x98,0xdb,0xa2,0xda,0x50,0xc8,0x81,
	0x53,0x07,0x1d,0x0e,0xa7,0x3f,0x48,0x57,0xea,0x5b,0x34,0x64,0x9f,0x0a,0x8b,0x36,
	0x7e,0x08,0xef,0x0f,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0xa8,0xd9,0xe6,0x7c,0x6e,0x90,0xea,0x0e,0xe5,0x2f,0xae,0xa9,
	0xf9,0x3e,0x04,0x58,0x66,0x7b,0x90,0x4d,0xc9,0xdd,0x1c,0x61,0x70,0x90,0xcb,0xe4,
	0xef,0x04,0x94,0xe0,0x79,0x14,0x48,0x14,0xbc,0xf4,0xe7,0x6b,0x16,0x33,0x3c,0xf5,
	0x36,0xed,0x9a,0x8d,0x0d,0x21,0x30,0x4f,0x72,0xb5,0x24,0x7f,0xb6,0xa9,0x76,0x40,
	0x05,0x93,0x64,0xe1,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x85,0x35,0x31,0x68,0x9e,0x40,0xb7,0x1a,0x34,0xd3,0x1e,0x84,
	0xf7,0x55,0x1d,0xf2,0x11,0x24,0x08,0x86,0x07,0x81,0xb1,0x8f,0xee,0xfe,0x6b,0x8b,
	0x43,0xa5,0x5b,0x8d,0xbd,0xd3,0x1e,0x09,0xee,0xf2,0xec,0x17,0x86,0xe6,0x1d,0x52,
	0x4f,0x8f,0x9d,0xe3,0xd3,0x7b,0x08,0x18,0x0d,0x74,0x07,0x3b,0x31,0x99,0x6e,0xa8,
	0x12,0xf5,0xa3,0x0b,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x23,0x60,0x23,0xc4,0x44,0x67,0x91,0xb7,0xde,0x06,0x9a,0x17,
	0x49,0x3a,0x8e,0x66,0xb4,0x54,0x61,0x4b,0xc4,0x9e,0xf8,0xe6,0xbc,0xf8,0x87,0xef,
	0x06,0xb5,0x40,0x4b,0xab,0xaf,0xf0,0xa0,0x46,0x43,0xc5,0xbd,0xec,0xff,0x57,0xfd,
	0x51,0x8a,0x6b,0x7b,0x32,0xee,0xeb,0x2f,0x81,0xd0,0xa0,0xa2,0x09,0x18,0xab,0x5c,
	0x85,0x1b,0x0f,0x57,};
unsigned char eccPublicKeyBuf[132] = {
	0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x0e,0x42,0x92,0x4a,0x1b,0x01,0xb6,0x64,0x89,0x97,0xfb,0x67,
	0x3f,0xa5,0xa6,0xc4,0xc4,0x82,0xa2,0xfa,0xe6,0x96,0xc9,0x0a,0x37,0xf2,0x44,0x6c,
	0xac,0x37,0x85,0x67,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0xf8,0xbb,0x32,0x55,0xe2,0x47,0x34,0x9a,0xc9,0xb5,0xdb,0xc7,
	0x17,0x4a,0xd9,0x84,0xbf,0xc5,0x3e,0x99,0x92,0xc6,0xd8,0x2d,0x6f,0xea,0xff,0x79,
	0x6b,0xde,0x3d,0x37,};
unsigned char eccPrivateKeyBuf[68] = {
	0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0xe6,0x51,0x2e,0xf8,0xca,0x14,0x84,0xa2,0xd9,0x76,0xc9,0x0d,
	0x37,0x1d,0xf1,0x95,0x49,0xbe,0x83,0x8e,0x70,0x09,0x1d,0x81,0xbd,0x6e,0xd9,0x5c,
	0xad,0x02,0x19,0x44,};


#if (SUPPORT_PRINTF)
static void vHtoA(uint8_t *pucSrc, uint16_t  usLen, uint8_t * pucDes)
{
	uint16_t i,j,mod=1;

	for(i=0,j=0; i<2*usLen; i+=2,j++)
	{
		mod = (pucSrc[j]>>4)&0x0F;
		if(mod<=9 && mod>=0)
			pucDes[i] = mod + 48;
		else
			pucDes[i] = mod + 55;

		mod = pucSrc[j]&0x0F;
		if(mod<=9 && mod>=0)
			pucDes[i+1] = mod + 48;
		else
			pucDes[i+1] = mod + 55;
	}
}
static void vdebug_hex_print(char * pcMsg,uint8_t *pucSendData, uint16_t sendlen)
{
	uint8_t ucAciiBuf[2048];

	memset(ucAciiBuf,0x00,sizeof(ucAciiBuf));
	if(sendlen > 1024)
	{
		sendlen = 1024;
	}
	if(sendlen != 0)
	{
		vHtoA(pucSendData,sendlen,ucAciiBuf);
		fprintf(stderr,"%s%s\n",pcMsg,ucAciiBuf);
	}
	else
	{
		fprintf(stderr,"%s\n",pcMsg);
	}
}
#endif

void Driver_GetInfo_Sata(char *disk_name)
{
    sg_io_hdr_t sg;
    uint8_t sense[32]; // how big should this be??
    uint8_t cdb[12];
	uint8_t buffer[1024],i;
    memset(&cdb, 0, sizeof (cdb));
    memset(&sense, 0, sizeof (sense));
    memset(&sg, 0, sizeof (sg));

    memset(buffer, 0, sizeof(buffer));

    cdb[0] = 0xa1; // ata pass through(12)
	cdb[1] = 4 << 1; // PIO DATA IN
	cdb[2] = 0x0E; // T_DIR = 1, BYTE_BLOCK = 1, Length in Sector Count
	sg.dxfer_direction = SG_DXFER_FROM_DEV;
	cdb[4] = 1;
	cdb[9] = 0xec; // IF_SEND/IF_RECV
    sg.interface_id = 'S';
    sg.cmd_len = sizeof (cdb);
    sg.mx_sb_len = sizeof (sense);
    sg.iovec_count = 0;
    sg.dxfer_len = 512;
    sg.dxferp = buffer;
    sg.cmdp = cdb;
    sg.sbp = sense;
    sg.timeout = 60000;
    sg.flags = 0;
    sg.pack_id = 0;
    sg.usr_ptr = NULL;

    if (ioctl(sDeviceHandle, SG_IO, &sg) < 0) {
		DRIVER_TRACE();
		debug_hex_print("Driver ioctl error\n",NULL,0);
        return;
    }
	//mode name
	for(i=0;i<MODULENAME_LEN;i+=2)
	{
		disk_name[i]= buffer[54+i+1];
		disk_name[i + 1]=  buffer[54+i];
	}
	disk_name[MODULENAME_LEN] = 0;
    return;
}
int8_t Driver_Transfer_Sata(uint8_t *SendBuffer, uint32_t SendLength, uint8_t *RecvBuffer, uint32_t *RecvLength)
{
    sg_io_hdr_t sg;
    uint8_t sense[32]; 
    uint8_t cdb[12];
	uint8_t sw1;
	uint8_t sw2;

    memset(&cdb, 0, sizeof (cdb));
    memset(&sense, 0, sizeof (sense));
    memset(&sg, 0, sizeof (sg));


	if(SendLength%512)
	{
		SendLength = (SendLength/512 + 1)*512;
	}
    cdb[0] = 0xa1; // ata pass through(12)
	cdb[1] = 5 << 1; // PIO DATA OUT
    cdb[2] = 0x06; // T_DIR = 0, BYTE_BLOCK = 1, Length in Sector Count
    sg.dxfer_direction = SG_DXFER_TO_DEV;

    cdb[3] = 0xC0; // ATA features / TRUSTED S/R security protocol
    cdb[4] = SendLength / 512; // Sector count / transfer length (512b blocks)
    //      cdb[5] = reserved;
    cdb[7] = 0x00;//((comID & 0xff00) >> 8);
    cdb[6] = 0x00;//(comID & 0x00ff);
    //      cdb[8] = 0x00;              // device
    cdb[9] = 0x5E; // IF_SEND/IF_RECV
    sg.interface_id = 'S';
    sg.cmd_len = sizeof (cdb);
    sg.mx_sb_len = sizeof (sense);
    sg.iovec_count = 0;
    sg.dxfer_len = SendLength;
    sg.dxferp = SendBuffer;
    sg.cmdp = cdb;
    sg.sbp = sense;
    sg.timeout = 60000;
    sg.flags = 0;
    sg.pack_id = 0;
    sg.usr_ptr = NULL;
    /*
     * Do the IO
     */
    if (ioctl(sDeviceHandle, SG_IO, &sg) < 0) {
    	DRIVER_TRACE();
		debug_hex_print("Driver ioctl error\n",NULL,0);
        return 0xff;
    }
	memset(&cdb, 0, sizeof (cdb));
    memset(&sense, 0, sizeof (sense));
    memset(&sg, 0, sizeof (sg));

	SendLength = TRANSFER_LEN;
	
    cdb[0] = 0xa1; // ata pass through(12)
    cdb[1] = 4 << 1; // PIO DATA IN
    cdb[2] = 0x0E; // T_DIR = 1, BYTE_BLOCK = 1, Length in Sector Count
    sg.dxfer_direction = SG_DXFER_FROM_DEV;
    cdb[3] = 0xC0; // ATA features / TRUSTED S/R security protocol
    cdb[4] = SendLength / 512; // Sector count / transfer length (512b blocks)
    //      cdb[5] = reserved;
    cdb[7] = 0x00;//((comID & 0xff00) >> 8);
    cdb[6] = 0x00;//(comID & 0x00ff);
    //      cdb[8] = 0x00;              // device
    cdb[9] = 0x5c; 
    sg.interface_id = 'S';
    sg.cmd_len = sizeof (cdb);
    sg.mx_sb_len = sizeof (sense);
    sg.iovec_count = 0;
    sg.dxfer_len = SendLength;
    sg.dxferp = RecvBuffer;
    sg.cmdp = cdb;
    sg.sbp = sense;
    sg.timeout = 60000;
    sg.flags = 0;
    sg.pack_id = 0;
    sg.usr_ptr = NULL;
    /*
     * Do the IO
     */
    if (ioctl(sDeviceHandle, SG_IO, &sg) < 0) {
    	DRIVER_TRACE();
		debug_hex_print("Driver ioctl error\n",NULL,0);
        return 0xff;
    }
	if(RecvBuffer[0] != 0x90 ||RecvBuffer[1]  != 0x00 )
	{
		*RecvLength = 2;
	}
	else
	{
		sw1= RecvBuffer[0];
		sw2= RecvBuffer[1];
	
		SendLength = (RecvBuffer[2]<<24)+ (RecvBuffer[3]<<16)+ (RecvBuffer[4]<<8)+RecvBuffer[5];
		if(SendLength > TRANSFER_LEN)
		{
			SendLength=TRANSFER_LEN - 6;
		}
		memmove(RecvBuffer,RecvBuffer+6,SendLength);
		RecvBuffer[SendLength] = sw1;
		RecvBuffer[SendLength+1] = sw2;
		*RecvLength = SendLength+2;
		memset(RecvBuffer + SendLength + 2, 0, TRANSFER_LEN - SendLength - 2);
	}	
    return 0;
}
void Driver_GetInfo_Nvme(char *disk_name)
{

	struct nvme_admin_cmd cmd;
    uint8_t ctrl[TRANSFER_LEN];
	int err;

	memset(&cmd, 0, sizeof(cmd));
	cmd.opcode = NVME_IDENTIFY;
	cmd.nsid = 0;
	cmd.addr = (unsigned long)&ctrl;
	cmd.data_len = TRANSFER_LEN;
	cmd.cdw10 = 1;
	err = ioctl(sDeviceHandle, NVME_IOCTL_ADMIN_CMD, &cmd);

	if (err) 
	{
		DRIVER_TRACE();
		debug_hex_print("Driver ioctl error\n",NULL,0);
		return;
	}
	memcpy(disk_name,ctrl+24,MODULENAME_LEN);

}
int8_t Driver_Transfer_Nvme(uint8_t *SendBuffer, uint32_t SendLength, uint8_t *RecvBuffer, uint32_t *RecvLength)
{
	struct nvme_admin_cmd nvme_cmd;
	uint8_t nvme_head[64];
	uint8_t nvme_sendbuf[64 + TRANSFER_LEN],sw1,sw2;
	int err;

	memset(nvme_head,0x00,sizeof(nvme_head));
	nvme_head[0] = 0xD1;
	memmove(nvme_sendbuf,nvme_head,sizeof(nvme_head));
	memmove(nvme_sendbuf + sizeof(nvme_head),SendBuffer,SendLength);
	SendLength +=sizeof(nvme_head);

	memset(&nvme_cmd, 0, sizeof(nvme_cmd));

	nvme_cmd.opcode = NVME_SECURITY_SEND;
	nvme_cmd.nsid=0x00;
	nvme_cmd.cdw10 = 0xFD00C100;
	nvme_cmd.cdw11 = SendLength;
	nvme_cmd.data_len = SendLength;
	nvme_cmd.addr = (__u64)nvme_sendbuf;
	//SEND
	err = ioctl(sDeviceHandle, NVME_IOCTL_ADMIN_CMD, &nvme_cmd);
	if (err < 0)
	{
		DRIVER_TRACE();
		debug_hex_print("Driver ioctl error1\n",NULL,0);
		return 1;
	}
	else if (err != 0) 
	{
		DRIVER_TRACE();
		debug_hex_print("Driver ioctl error2\n",(uint8_t *)&err,4);
		return 2;
	}
	else
	{
		//REV
		memset(&nvme_cmd, 0, sizeof(nvme_cmd));
		SendLength = TRANSFER_LEN;
		nvme_cmd.nsid=0x00;
		nvme_cmd.opcode = NVME_SECURITY_RECV;
		nvme_cmd.cdw10 = 0xFD00C100 ;
		nvme_cmd.cdw11 = SendLength;
		nvme_cmd.data_len = SendLength;
		nvme_cmd.addr = (__u64)RecvBuffer;

		err = ioctl(sDeviceHandle, NVME_IOCTL_ADMIN_CMD, &nvme_cmd);
		if (err < 0)
		{
			DRIVER_TRACE();
			debug_hex_print("Driver ioctl error3\n",NULL,0);
			return 1;
		}
		else if (err != 0) 
		{
			DRIVER_TRACE();
			debug_hex_print("Driver ioctl error4\n",NULL,0);
			return 2;
		}
		else
		{
			memmove(RecvBuffer,RecvBuffer+64,TRANSFER_LEN - 64);
			if(RecvBuffer[0] != 0x90 ||RecvBuffer[1]  != 0x00 )
			{
				*RecvLength = 2;
			}
			else
			{
				sw1= RecvBuffer[0];
				sw2= RecvBuffer[1];
			
				SendLength = (RecvBuffer[2]<<24)+ (RecvBuffer[3]<<16)+ (RecvBuffer[4]<<8)+RecvBuffer[5];
				if(SendLength > TRANSFER_LEN)
				{
					SendLength=TRANSFER_LEN - 6;
				}
				memmove(RecvBuffer,RecvBuffer+6,SendLength);
				RecvBuffer[SendLength] = sw1;
				RecvBuffer[SendLength+1] = sw2;
				*RecvLength = SendLength+2;
				memset(RecvBuffer + SendLength + 2, 0, TRANSFER_LEN - SendLength - 2);
			}	
			return 0;
		}
	}

}


void Driver_OpenDevice(const char * devref)
{
    if (access(devref, R_OK | W_OK)) 
	{
		DRIVER_TRACE();
		debug_hex_print("Driver RW error\n",NULL,0);
		return;
    }
	sDeviceHandle = open(devref, O_RDWR);
    if (sDeviceHandle < 0) 
	{
		isOpen = FALSE;
		DRIVER_TRACE();
		debug_hex_print("Driver open device error\n",NULL,0);
    }
	else
	{
		isOpen = TRUE;
	}
}
void Driver_CloseDevice(void)
{
	if(isOpen)
	{
		close(sDeviceHandle);
	}
	isOpen = FALSE;
}
uint8_t Driver_ScanDevice(void)
{
    DIR *dir;
    struct dirent *dirent;
    char devname[25];
	char modulename[MODULENAME_LEN + 1];
    char all_devicename[400],devicecnt;
	uint16_t i;

	memset(all_devicename,0x00,sizeof(all_devicename));
	devicecnt =0;
    dir = opendir("/dev");

    if(dir!=NULL)
    {
        while((dirent=readdir(dir))!=NULL) 
		{
            if((!fnmatch("sd[a-z]",dirent->d_name,0)) || (!fnmatch("nvme[0-9]",dirent->d_name,0)) ||(!fnmatch("nvme[0-9][0-9]",dirent->d_name,0))) 
			{
				strcpy(all_devicename + devicecnt*MODULENAME_LEN,dirent->d_name);
                devicecnt++;
            }
        }
        closedir(dir);
    }
    for(i = 0; i < devicecnt; i++) 
	{
        snprintf(devname,23,"/dev/%s",all_devicename + i*MODULENAME_LEN);
		Driver_OpenDevice(devname);
		if(isOpen)
		{
			if (!strncmp(devname, "/dev/nvme", 9))
			{
				Driver_GetInfo_Nvme(modulename);
				debug_hex_print(modulename,NULL,0);
				if(strstr(modulename, "DATSSD"))
				{
					device_type = DEVICE_NVME;
					return TRUE;
				}
			}
			else if (!strncmp(devname, "/dev/s", 6))
			{
				Driver_GetInfo_Sata(modulename);
				debug_hex_print(modulename,NULL,0);
				if(strstr(modulename, "DATSSD"))
				{
					device_type = DEVICE_SATA;
					return TRUE;
				}
			}
			else
			{
				debug_hex_print("unknown drive type\n",NULL,0);
				
			}
		}
    }
	DRIVER_TRACE();
	return FALSE;
}
int8_t Driver_Transfer(uint8_t *SendBuffer, uint32_t SendLength, uint8_t *RecvBuffer, uint32_t *RecvLength)
{
	int8_t ret;
	debug_hex_print("//APDU command from PC:\n",SendBuffer,SendLength);
	if(device_type == DEVICE_SATA)
	{
		ret = Driver_Transfer_Sata(SendBuffer, SendLength,RecvBuffer,RecvLength);
	}
	else if(device_type == DEVICE_NVME)
	{
		ret = Driver_Transfer_Nvme(SendBuffer, SendLength,RecvBuffer,RecvLength);
	}
	else
	{
		ret = 1;
		DRIVER_TRACE();
		debug_hex_print("unknown drive type\n",NULL,0);
		
	}
	if(*RecvLength == 2)
	{
		debug_hex_print("//APDU response status from device :\n",RecvBuffer,*RecvLength);
	}
	else
	{
		debug_hex_print("//APDU response data from device:\n",RecvBuffer,*RecvLength - 2);
		debug_hex_print("//APDU response status from device:\n",RecvBuffer + *RecvLength - 2,2);
	}
	return ret;
}
int SDF_OpenDevice(
	void **phDeviceHandle)
{
	if (!phDeviceHandle /* || !(*phDeviceHandle) */)
		return SDR_INARGERR;

	if(FALSE == Driver_ScanDevice())
	{
		SDF_TRACE();
		*phDeviceHandle = NULL;
		return SDR_OPENDEVICE;
	}
	sdf_deviceHandle = "Device Handle ok";
	*phDeviceHandle = sdf_deviceHandle;
	return SDR_OK;
}

int SDF_CloseDevice(
	void *hDeviceHandle)
{
	SDF_TRACE();
	Driver_CloseDevice();
	sdf_deviceHandle = NULL;
	hDeviceHandle = NULL;
	return SDR_OK;
}

int SDF_OpenSession(
	void *hDeviceHandle,
	void **phSessionHandle)
{
	SDF_TRACE();
	if (!phSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if (!hDeviceHandle)
	{
		return SDR_OPENDEVICE;
	}
	sessionHandle = "SDF Session Handle";
	if(SDR_OK != SDF_GetPrivateKeyAccessRight(sessionHandle,0,(unsigned char *)"123456",0x06))
	{
		return SDR_UNKNOWERR;	
	}
	*phSessionHandle = sessionHandle;
	return SDR_OK;
}

int SDF_CloseSession(
	void *hSessionHandle)
{
	SDF_TRACE();
	sessionHandle = NULL;
	hSessionHandle = NULL;
	return SDR_OK;
}

#define SDF_DEV_DATE		"20220101"
#define SDF_DEV_BATCH_NUM	"001"
#define SDF_DEV_SERIAL_NUM	"123456"
#define SDF_DEV_SERIAL		SDF_DEV_DATE \
				SDF_DEV_BATCH_NUM \
				SDF_DEV_SERIAL_NUM

int SDF_GetDeviceInfo(
	void *hSessionHandle,
	DEVICEINFO *pstDeviceInfo)
{
	SDF_TRACE();
	#if(SUPPORT_FUCTION > 0)
	//uint32_t revlen;
	ECCrefPublicKey sm2_pubkey;
	ECCrefPrivateKey sm2_prikey;
	uint8_t test_hashdata[2]={0x01,0x01},test_hashresult[32];
	ECCSignature sm2_sign;
	ECCCipher   sm2_Cipher;
	uint32_t hashLen;
	uint8_t enc_data[32],ucIv[16],dec_data[32],sm4_key[32];

	if (!pstDeviceInfo)
		return SDR_OPENSESSION;
	// memset(s_SDF_SendBuf,0x00,sizeof(s_SDF_SendBuf));
	// CLA = cla_securify;
	// INS = ins_device_info;
	// P1 = 0x00;
	// P2 = 0x00;
	// P3 = 0x00;
	// Driver_Transfer(s_SDF_SendBuf, 5, s_SDF_RevBuf,&revlen);
	// if(SDR_OK !=SDF_GenerateRandom(hSessionHandle,0x08,s_SDF_RevBuf))
	// {
	// 	return SDR_UNKNOWERR;	
	// }
	if(SDR_OK !=SDF_ReleasePrivateKeyAccessRight(hSessionHandle,0))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK != SDF_GetPrivateKeyAccessRight(hSessionHandle,0,(unsigned char *)"123456",0x06))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_ExportSignPublicKey_ECC(hSessionHandle,0,&sm2_pubkey))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_ExportEncPublicKey_ECC(hSessionHandle,0,&sm2_pubkey))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_GenerateKeyPair_ECC(hSessionHandle,SGD_SM2,ECC_BIT_LEN,&sm2_pubkey,&sm2_prikey))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_HashInit(hSessionHandle,SGD_SM3,NULL,NULL,0))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_HashUpdate(hSessionHandle,test_hashdata,2))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_HashFinal(hSessionHandle,test_hashresult,&hashLen))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_InternalSign_ECC(hSessionHandle,0x0010,test_hashresult,32,&sm2_sign))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_InternalVerify_ECC(hSessionHandle,0x0010,test_hashresult,32,&sm2_sign))
	{
		return SDR_UNKNOWERR;	
	}
	memset(test_hashresult,0x01,32);
	memset(dec_data,0x00,32);
	//External sign 
	if(SDR_OK !=SDF_ExternalSign_ECC(hSessionHandle,SGD_SM2,&sm2_prikey,test_hashresult,32,&sm2_sign))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_ExternalVerify_ECC(hSessionHandle,SGD_SM2,&sm2_pubkey,test_hashresult,32,&sm2_sign))
	{
		return SDR_UNKNOWERR;	
	}
	memset(test_hashresult,0x01,32);
	memset(dec_data,0x00,32);
	// //External enc dec
	if(SDR_OK !=SDF_ExternalEncrypt_ECC(hSessionHandle,SGD_SM2,&sm2_pubkey,test_hashresult,32,&sm2_Cipher))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_ExternalDecrypt_ECC(hSessionHandle,SGD_SM2,&sm2_prikey,&sm2_Cipher,dec_data,&hashLen))
	{
		return SDR_UNKNOWERR;	
	}
	if(memcmp(dec_data,test_hashresult,32))
	{
		return SDR_UNKNOWERR;	
	}
	memset(test_hashresult,0x11,32);
	memset(dec_data,0x11,32);
	memset(ucIv,0x11,16);
	memset(sm4_key,0x11,16);
	//sm4
	if(SDR_OK !=SDF_Encrypt(hSessionHandle,sm4_key,SGD_SM4_ECB,ucIv,test_hashresult,32,enc_data,&hashLen))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_Decrypt(hSessionHandle,sm4_key,SGD_SM4_ECB,ucIv,enc_data,32,dec_data,&hashLen))
	{
		return SDR_UNKNOWERR;	
	}
	if(memcmp(dec_data,test_hashresult,32))
	{
		return SDR_UNKNOWERR;	
	}
	memset(test_hashresult,0x11,32);
	memset(dec_data,0x11,32);
	memset(ucIv,0x11,16);
	memset(sm4_key,0x11,16);
	//sm4
	if(SDR_OK !=SDF_Encrypt(hSessionHandle,sm4_key,SGD_SM4_CBC,ucIv,test_hashresult,16,enc_data,&hashLen))
	{
		return SDR_UNKNOWERR;	
	}
	if(SDR_OK !=SDF_Decrypt(hSessionHandle,sm4_key,SGD_SM4_CBC,ucIv,enc_data,16,dec_data,&hashLen))
	{
		return SDR_UNKNOWERR;	
	}
	if(memcmp(dec_data,test_hashresult,16))
	{
		return SDR_UNKNOWERR;	
	}
	#endif

	memset(pstDeviceInfo, 0, sizeof(*pstDeviceInfo));
	strncpy((char *)pstDeviceInfo->IssuerName, "DATSSD",
		sizeof(pstDeviceInfo->IssuerName));
	strncpy((char *)pstDeviceInfo->DeviceName, "DATSSD ENCARD",
		sizeof(pstDeviceInfo->DeviceName));
	strncpy((char *)pstDeviceInfo->DeviceSerial, SDF_DEV_SERIAL,
		sizeof(pstDeviceInfo->DeviceSerial));
	pstDeviceInfo->DeviceVersion = 1000;
	pstDeviceInfo->StandardVersion = 1000;
	pstDeviceInfo->AsymAlgAbility[0] = SGD_SM2_1|SGD_SM2_3;
	pstDeviceInfo->AsymAlgAbility[1] = 256|512|1024|2048|4096;
	pstDeviceInfo->SymAlgAbility = SGD_SM4|SGD_ECB|SGD_CBC;
	pstDeviceInfo->HashAlgAbility = SGD_SM3|SGD_SHA256;
	pstDeviceInfo->BufferSize = TRANSFER_LEN;
	return SDR_OK;
}

int SDF_GenerateRandom(
	void *hSessionHandle,
	unsigned int uiLength,
	unsigned char *pucRandom)
{
	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	CLA = cla_securify;
	INS = ins_get_random;
	P1 = 0x00;
	P2 = 0x00;
	P3 = 0x00;
	DATA_BUF[0]= (uiLength>>8)&0xFF;
	DATA_BUF[1]= uiLength&0xFF;
	if(Driver_Transfer(s_SDF_SendBuf, 7, s_SDF_RevBuf,&uiLength) || (s_SDF_RevBuf[uiLength - 2] != 0x90 ||s_SDF_RevBuf[uiLength - 1] != 0x00))
	{
		return SDR_RANDERR;
	}
	memcpy(pucRandom,s_SDF_RevBuf,uiLength - 2);
	return SDR_OK;
}

int SDF_GetPrivateKeyAccessRight(
	void *hSessionHandle,
	unsigned int uiKeyIndex,
	unsigned char *pucPassword,
	unsigned int uiPwdLength)
{
	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	CLA = cla_securify;
	INS = ins_pin_verify;
	P1 = 0x00;
	P2 = uiKeyIndex&0xFF;
	P3 = 0x00;
	DATA_BUF[0]= (uiPwdLength>>8)&0xFF;
	DATA_BUF[1]= uiPwdLength&0xFF;
	memmove(DATA_BUF + 2,pucPassword,uiPwdLength);
	if(Driver_Transfer(s_SDF_SendBuf, 7 + uiPwdLength, s_SDF_RevBuf,&uiPwdLength) || (s_SDF_RevBuf[uiPwdLength - 2] != 0x90 ||s_SDF_RevBuf[uiPwdLength - 1]  != 0x00))
	{
		return SDR_VERIFYERR;
	}
	return SDR_OK;
}

int SDF_ReleasePrivateKeyAccessRight(
	void *hSessionHandle,
	unsigned int uiKeyIndex)
{
	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	CLA = cla_securify;
	INS = ins_pin_logout;
	P1 = 0x00;
	P2 = uiKeyIndex&0xFF;
	P3 = 0x00;
	if(Driver_Transfer(s_SDF_SendBuf, 5, s_SDF_RevBuf,&uiKeyIndex) || (s_SDF_RevBuf[uiKeyIndex - 2] != 0x90 ||s_SDF_RevBuf[uiKeyIndex - 1]  != 0x00))
	{
		return SDR_VERIFYERR;
	}
	return SDR_OK;
}

int SDF_ExportSignPublicKey_RSA(
	void *hSessionHandle,
	unsigned int uiKeyIndex,
	RSArefPublicKey *pucPublicKey)
{
	if (!pucPublicKey)
		return SDR_INARGERR;
	memcpy(pucPublicKey, rsaPublicKeyBuf, sizeof(*pucPublicKey));
	return SDR_OK;
}

int SDF_ExportEncPublicKey_RSA(
	void *hSessionHandle,
	unsigned int uiKeyIndex,
	RSArefPublicKey *pucPublicKey)
{
	if (!pucPublicKey)
		return SDR_INARGERR;
	memcpy(pucPublicKey, rsaPublicKeyBuf, sizeof(*pucPublicKey));
	return SDR_OK;
}

int SDF_GenerateKeyPair_RSA(
	void *hSessionHandle,
	unsigned int uiKeyBits,
	RSArefPublicKey *pucPublicKey,
	RSArefPrivateKey *pucPrivateKey)
{
	if (!pucPublicKey || !pucPrivateKey)
		return SDR_INARGERR;
	memcpy(pucPublicKey, rsaPublicKeyBuf, sizeof(*pucPublicKey));
	memcpy(pucPrivateKey, rsaPrivateKeyBuf, sizeof(*pucPrivateKey));
	return SDR_OK;
}

int SDF_GenerateKeyWithIPK_RSA(
	void *hSessionHandle,
	unsigned int uiIPKIndex,
	unsigned int uiKeyBits,
	unsigned char *pucKey,
	unsigned int *puiKeyLength,
	void **phKeyHandle)
{
	if (!puiKeyLength)
		return SDR_INARGERR;
	*puiKeyLength = 2048/8;
	if (phKeyHandle && *phKeyHandle)
		*phKeyHandle = keyHandle;
	return SDR_OK;
}

int SDF_GenerateKeyWithEPK_RSA(
	void *hSessionHandle,
	unsigned int uiKeyBits,
	RSArefPublicKey *pucPublicKey,
	unsigned char *pucKey,
	unsigned int *puiKeyLength,
	void **phKeyHandle)
{
	if (!puiKeyLength)
		return SDR_INARGERR;
	*puiKeyLength = 2048/8;
	if (phKeyHandle && *phKeyHandle)
		*phKeyHandle = keyHandle;
	return SDR_OK;
}

int SDF_ImportKeyWithISK_RSA(
	void *hSessionHandle,
	unsigned int uiISKIndex,
	unsigned char *pucKey,
	unsigned int uiKeyLength,
	void **phKeyHandle)
{
	if (!phKeyHandle || !(*phKeyHandle))
		return SDR_INARGERR;
	*phKeyHandle = keyHandle;
	return SDR_OK;
}

int SDF_ExchangeDigitEnvelopeBaseOnRSA(
	void *hSessionHandle,
	unsigned int uiKeyIndex,
	RSArefPublicKey *pucPublicKey,
	unsigned char *pucDEInput,
	unsigned int uiDELength,
	unsigned char *pucDEOutput,
	unsigned int *puiDELength)
{
	if (!puiDELength)
		return SDR_INARGERR;
	*puiDELength = 2048/8;
	return SDR_OK;
}

int SDF_ExportSignPublicKey_ECC(
	void *hSessionHandle,
	unsigned int uiKeyIndex,
	ECCrefPublicKey *pucPublicKey)
{
	SDF_TRACE();
	if (!pucPublicKey)
	{
		return SDR_INARGERR;
	}
	CLA = cla_securify;
	INS = ins_asy_export;
	P1 = 0x01;
	P2 = 0x00;
	P3 = 0x00;
	if(Driver_Transfer(s_SDF_SendBuf, 5, s_SDF_RevBuf,&uiKeyIndex) || (s_SDF_RevBuf[uiKeyIndex - 2] != 0x90 ||s_SDF_RevBuf[uiKeyIndex - 1]  != 0x00))
	{
		return SDR_SYMOPERR;
	}
	pucPublicKey->bits=ECC_BIT_LEN;
	memcpy(pucPublicKey->x, s_SDF_RevBuf, ECC_BIT_LEN/8);
	memcpy(pucPublicKey->y, s_SDF_RevBuf + (ECC_BIT_LEN/8), ECC_BIT_LEN/8);
	return SDR_OK;
}

int SDF_ExportEncPublicKey_ECC(
	void *hSessionHandle,
	unsigned int uiKeyIndex,
	ECCrefPublicKey *pucPublicKey)
{
	SDF_TRACE();
	if (!pucPublicKey)
	{
		return SDR_INARGERR;
	}
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	CLA = cla_securify;
	INS = ins_asy_export;
	P1 = 0x01;
	P2 = 0x01;
	P3 = 0x00;
	if(Driver_Transfer(s_SDF_SendBuf, 5, s_SDF_RevBuf,&uiKeyIndex) || (s_SDF_RevBuf[uiKeyIndex - 2] != 0x90 ||s_SDF_RevBuf[uiKeyIndex - 1]  != 0x00))
	{
		return SDR_SYMOPERR;
	}
	pucPublicKey->bits=ECC_BIT_LEN;
	memcpy(pucPublicKey->x, s_SDF_RevBuf, ECC_BIT_LEN/8);
	memcpy(pucPublicKey->y, s_SDF_RevBuf + (ECC_BIT_LEN/8), ECC_BIT_LEN/8);
	return SDR_OK;
}

int SDF_GenerateKeyPair_ECC(
	void *hSessionHandle,
	unsigned int uiAlgID,
	unsigned int  uiKeyBits,
	ECCrefPublicKey *pucPublicKey,
	ECCrefPrivateKey *pucPrivateKey)
{
	uint revlen;

	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if (!pucPublicKey)
	{
		return SDR_INARGERR;
	}
	if(uiAlgID != SGD_SM2)
	{
		return SDR_INARGERR;
	}
	if(uiKeyBits != ECC_BIT_LEN)
	{
		return SDR_INARGERR;
	}
	CLA = cla_securify;
	INS = ins_asy_gen;
	P1 = 0x01;
	P2 = 0x03;
	P3 = 0x02;
	DATA_BUF[0]=(uiKeyBits>>8)&0xFF;
	DATA_BUF[1]=uiKeyBits&0xFF;
	if(Driver_Transfer(s_SDF_SendBuf, 7, s_SDF_RevBuf,&revlen) || (s_SDF_RevBuf[revlen - 2] != 0x90 ||s_SDF_RevBuf[revlen - 1]  != 0x00))
	{
		return SDR_SYMOPERR;
	}
	pucPublicKey->bits=ECC_BIT_LEN;
	memcpy(pucPublicKey->x, s_SDF_RevBuf, ECC_BIT_LEN/8);
	memcpy(pucPublicKey->y, s_SDF_RevBuf + (ECC_BIT_LEN/8), ECC_BIT_LEN/8);
	pucPrivateKey->bits=ECC_BIT_LEN;
	memcpy(pucPrivateKey->K, s_SDF_RevBuf + (ECC_BIT_LEN/8) + (ECC_BIT_LEN/8), ECC_BIT_LEN/8);

	return SDR_OK;
}

int SDF_GenerateKeyWithIPK_ECC(
	void *hSessionHandle,
	unsigned int uiIPKIndex,
	unsigned int uiKeyBits,
	ECCCipher *pucKey,
	void **phKeyHandle)
{
	if (!phKeyHandle || !(*phKeyHandle))
		return SDR_INARGERR;
	*phKeyHandle = keyHandle;
	return SDR_OK;
}

int SDF_GenerateKeyWithEPK_ECC(
	void *hSessionHandle,
	unsigned int uiKeyBits,
	unsigned int uiAlgID,
	ECCrefPublicKey *pucPublicKey,
	ECCCipher *pucKey,
	void **phKeyHandle)
{
	if (!phKeyHandle || !(*phKeyHandle))
		return SDR_INARGERR;
	*phKeyHandle = keyHandle;
	return SDR_OK;
}

int SDF_ImportKeyWithISK_ECC(
	void *hSessionHandle,
	unsigned int uiISKIndex,
	ECCCipher *pucKey,
	void **phKeyHandle)
{
	if (!phKeyHandle || !(*phKeyHandle))
		return SDR_INARGERR;
	*phKeyHandle = keyHandle;
	return SDR_OK;
}

/* 6.3.14 */
int SDF_GenerateAgreementDataWithECC(
	void *hSessionHandle,
	unsigned int uiISKIndex,
	unsigned int uiKeyBits,
	unsigned char *pucSponsorID,
	unsigned int uiSponsorIDLength,
	ECCrefPublicKey *pucSponsorPublicKey,
	ECCrefPublicKey *pucSponsorTmpPublicKey,
	void **phAgreementHandle)
{
	// any output public key ?
	if (!phAgreementHandle || !(*phAgreementHandle))
		return SDR_INARGERR;
	*phAgreementHandle = agreementHandle;
	return SDR_OK;
}

/* 6.3.15 */
int SDF_GenerateKeyWithECC(
	void *hSessionHandle,
	unsigned char *pucResponseID,
	unsigned int uiResponseIDLength,
	ECCrefPublicKey *pucResponsePublicKey,
	ECCrefPublicKey *pucResponseTmpPublicKey,
	void *hAgreementHandle,
	void **phKeyHandle)
{
	if (!phKeyHandle || !(*phKeyHandle))
		return SDR_INARGERR;
	*phKeyHandle = keyHandle;
	return SDR_OK;
}

/* 6.3.16 */
int SDF_GenerateAgreementDataAndKeyWithECC(
	void *hSessionHandle,
	unsigned int uiISKIndex,
	unsigned int uiKeyBits,
	unsigned char *pucResponseID,
	unsigned int uiResponseIDLength,
	unsigned char *pucSponsorID,
	unsigned int uiSponsorIDLength,
	ECCrefPublicKey *pucSponsorPublicKey,
	ECCrefPublicKey *pucSponsorTmpPublicKey,
	ECCrefPublicKey *pucResponsePublicKey,
	ECCrefPublicKey *pucResponseTmpPublicKey,
	void **phKeyHandle)
{
	// any output
	if (!phKeyHandle || !(*phKeyHandle))
		return SDR_INARGERR;
	*phKeyHandle = keyHandle;
	return SDR_OK;
}

int SDF_ExchangeDigitEnvelopeBaseOnECC(
	void *hSessionHandle,
	unsigned int uiKeyIndex,
	unsigned int uiAlgID,
	ECCrefPublicKey *pucPublicKey,
	ECCCipher *pucEncDataIn,
	ECCCipher *pucEncDataOut)
{
	return SDR_OK;
}

int SDF_GenerateKeyWithKEK(
	void *hSessionHandle,
	unsigned int uiKeyBits,
	unsigned int uiAlgID,
	unsigned int uiKEKIndex,
	unsigned char *pucKey,
	unsigned int *puiKeyLength,
	void **phKeyHandle)
{
	if (!phKeyHandle || !(*phKeyHandle))
		return SDR_INARGERR;
	*phKeyHandle = keyHandle;
	return SDR_OK;
}

int SDF_ImportKeyWithKEK(
	void *hSessionHandle,
	unsigned int uiAlgID,
	unsigned int uiKEKIndex,
	unsigned char *pucKey,
	unsigned int uiKeyLength,
	void **phKeyHandle)
{
	if (!phKeyHandle || !(*phKeyHandle))
		return SDR_INARGERR;
	*phKeyHandle = keyHandle;
	return SDR_OK;
}

int SDF_DestroyKey(
	void *hSessionHandle,
	void *hKeyHandle)
{
	return SDR_OK;
}

int SDF_ExternalPublicKeyOperation_RSA(
	void *hSessionHandle,
	RSArefPublicKey *pucPublicKey,
	unsigned char *pucDataInput,
	unsigned int uiInputLength,
	unsigned char *pucDataOutput,
	unsigned int *puiOutputLength)
{
	if (!puiOutputLength)
		return SDR_INARGERR;
	*puiOutputLength = 2048/8;
	return SDR_OK;
}

int SDF_ExternalPrivateKeyOperation_RSA(
	void *hSessionHandle,
	RSArefPrivateKey *pucPrivateKey,
	unsigned char *pucDataInput,
	unsigned int uiInputLength,
	unsigned char *pucDataOutput,
	unsigned int *puiOutputLength)
{
	if (!puiOutputLength)
		return SDR_INARGERR;
	*puiOutputLength = 2048/8;
	return SDR_OK;
}

int SDF_InternalPrivateKeyOperation_RSA(
	void *hSessionHandle,
	unsigned int uiKeyIndex,
	unsigned char *pucDataInput,
	unsigned int uiInputLength,
	unsigned char *pucDataOutput,
	unsigned int *puiOutputLength)
{
	if (!puiOutputLength)
		return SDR_INARGERR;
	*puiOutputLength = 2048/8;
	return SDR_OK;
}
int SDF_ExternalSign_ECC(				
		void* hSessionHandle,
		unsigned int uiAlgID,
		ECCrefPrivateKey *pucPrivateKey,
		unsigned char *pucData,
		unsigned int uiDataLength,
		ECCSignature *pucSignature)
{
	uint8_t ucOffset;

	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if (!pucPrivateKey)
	{
		return SDR_INARGERR;
	}
	if(uiAlgID != SGD_SM2)
	{
		return SDR_INARGERR;
	}
	if(uiDataLength != (ECC_BIT_LEN/8))
	{
		return SDR_INARGERR;
	}
	CLA = cla_securify;
	INS = ins_asy_sign;
	P1 = 0x01;
	P2 = 0x02;
	P3 = (ECC_BIT_LEN/8)*2;
	ucOffset = 0;
	memmove(DATA_BUF,pucPrivateKey->K,ECC_BIT_LEN/8);
	ucOffset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + ucOffset,pucData,ECC_BIT_LEN/8);
	ucOffset +=ECC_BIT_LEN/8;

	if(Driver_Transfer(s_SDF_SendBuf, 5 + ucOffset, s_SDF_RevBuf,&uiDataLength) || (s_SDF_RevBuf[uiDataLength - 2] != 0x90 ||s_SDF_RevBuf[uiDataLength - 1]  != 0x00))
	{
		return SDR_SIGNERR;
	}
	memmove(pucSignature->r, s_SDF_RevBuf, ECC_BIT_LEN/8);
	memmove(pucSignature->s, s_SDF_RevBuf + ECC_BIT_LEN/8,ECC_BIT_LEN/8);
	return SDR_OK;
}

int SDF_ExternalVerify_ECC(
	void *hSessionHandle,
	unsigned int uiAlgID,
	ECCrefPublicKey *pucPublicKey,
	unsigned char *pucDataInput,
	unsigned int uiInputLength,
	ECCSignature *pucSignature)
{
	uint8_t ucOffset;

	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if (!pucPublicKey)
	{
		return SDR_INARGERR;
	}
	if(uiAlgID != SGD_SM2)
	{
		return SDR_INARGERR;
	}
	if(uiInputLength != (ECC_BIT_LEN/8))
	{
		return SDR_INARGERR;
	}
	CLA = cla_securify;
	INS = ins_asy_verify;
	P1 = 0x01;
	P2 = 0x02;
	P3 = (ECC_BIT_LEN/8)*5;
	ucOffset = 0;
	memmove(DATA_BUF,pucPublicKey->x,ECC_BIT_LEN/8);
	ucOffset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + ucOffset,pucPublicKey->y,ECC_BIT_LEN/8);
	ucOffset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + ucOffset,pucSignature->r,ECC_BIT_LEN/8);
	ucOffset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + ucOffset,pucSignature->s,ECC_BIT_LEN/8);
	ucOffset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + ucOffset,pucDataInput,uiInputLength);

	if(Driver_Transfer(s_SDF_SendBuf, 5 + (ECC_BIT_LEN/8)*4 + uiInputLength, s_SDF_RevBuf,&uiInputLength) || (s_SDF_RevBuf[uiInputLength - 2] != 0x90 ||s_SDF_RevBuf[uiInputLength - 1]  != 0x00))
	{
		return SDR_VERIFYERR;
	}
	return SDR_OK;
}

int SDF_InternalSign_ECC(
	void *hSessionHandle,
	unsigned int uiISKIndex,
	unsigned char *pucData,
	unsigned int uiDataLength,
	ECCSignature *pucSignature)
{
	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if (!pucSignature)
	{
		return SDR_INARGERR;
	}
	if(uiDataLength != ECC_BIT_LEN/8)
	{
		return SDR_INARGERR;
	}
	CLA = cla_securify;
	INS = ins_asy_sign;
	P1 = 0x01;
	P2 = 0x01;
	P3 = uiDataLength + 2;
	DATA_BUF[0] = (uiISKIndex>>8)&0xFF;
	DATA_BUF[1] = uiISKIndex&0xFF;
	memmove(DATA_BUF + 2, pucData, uiDataLength);

	if(Driver_Transfer(s_SDF_SendBuf, 5 + 2 + uiDataLength , s_SDF_RevBuf, &uiDataLength) || (s_SDF_RevBuf[uiDataLength - 2] != 0x90 ||s_SDF_RevBuf[uiDataLength - 1]  != 0x00))
	{
		return SDR_SIGNERR;
	}
	memmove(pucSignature->r, s_SDF_RevBuf, ECC_BIT_LEN/8);
	memmove(pucSignature->s, s_SDF_RevBuf + ECC_BIT_LEN/8,ECC_BIT_LEN/8);
	return SDR_OK;
}

int SDF_InternalVerify_ECC(
	void *hSessionHandle,
	unsigned int uiIPKIndex,
	unsigned char *pucData,
	unsigned int uiDataLength,
	ECCSignature *pucSignature)
{
	uint8_t ucOffset;
	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if (!pucSignature)
	{
		return SDR_INARGERR;
	}
	if(uiDataLength != (ECC_BIT_LEN/8))
	{
		return SDR_INARGERR;
	}
	memset(s_SDF_SendBuf,0x00,sizeof(s_SDF_SendBuf));
	CLA = cla_securify;
	INS = ins_asy_verify;
	P1 = 0x01;
	P2 = 0x01;
	P3 = 2 + (ECC_BIT_LEN/8)*3;
	DATA_BUF[0] = (uiIPKIndex>>8)&0xFF;
	DATA_BUF[1] = uiIPKIndex&0xFF;
	ucOffset = 2;
	memmove(DATA_BUF + ucOffset,pucSignature->r,ECC_BIT_LEN/8);
	ucOffset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + ucOffset,pucSignature->s,ECC_BIT_LEN/8);
	ucOffset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + ucOffset,pucData,ECC_BIT_LEN/8);

	if(Driver_Transfer(s_SDF_SendBuf, 5 + (ECC_BIT_LEN/8)*3 + 2, s_SDF_RevBuf,&uiDataLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[uiDataLength - 2] != 0x90 ||s_SDF_RevBuf[uiDataLength - 1]  != 0x00)
	{
		return SDR_VERIFYERR;
	}
	return SDR_OK;
}

int SDF_ExternalEncrypt_ECC(
	void *hSessionHandle,
	unsigned int uiAlgID,
	ECCrefPublicKey *pucPublicKey,
	unsigned char *pucData,
	unsigned int uiDataLength,
	ECCCipher *pucEncData)
{
	uint32_t Offset;

	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if(!pucEncData || !pucData|| !pucPublicKey)
	{
		return SDR_INARGERR;
	}
	if(uiAlgID != SGD_SM2)
	{
		return SDR_INARGERR;
	}
	if(pucPublicKey->bits != ECC_BIT_LEN)
	{
		return SDR_INARGERR;
	}

	CLA = cla_securify;
	INS = ins_asy_enc;
	P1 = 0x01;
	P2 = 0x02;
	P3 = 0x00;
	Offset = 2;
	memmove(DATA_BUF + Offset,pucPublicKey->x,ECC_BIT_LEN/8);
	Offset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + Offset,pucPublicKey->y,ECC_BIT_LEN/8);
	Offset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + Offset,pucData,uiDataLength);

	uiDataLength +=((ECC_BIT_LEN/8)*2);
	DATA_BUF[0] = (uiDataLength>>8)&0xFF;
	DATA_BUF[1] = uiDataLength&0xFF;

	if(Driver_Transfer(s_SDF_SendBuf, 7 + uiDataLength, s_SDF_RevBuf,&uiDataLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[uiDataLength - 2] != 0x90 ||s_SDF_RevBuf[uiDataLength - 1]  != 0x00)
	{
		return SDR_PKOPERR;
	}
	//04+c1c3c2
	Offset=1;
	memmove(pucEncData->x,s_SDF_RevBuf + Offset,ECC_BIT_LEN/8);
	Offset +=ECC_BIT_LEN/8;
	memmove(pucEncData->y,s_SDF_RevBuf + Offset,ECC_BIT_LEN/8);
	Offset +=ECC_BIT_LEN/8;
	memmove(pucEncData->M,s_SDF_RevBuf + Offset,ECC_BIT_LEN/8);
	Offset +=ECC_BIT_LEN/8;
	memmove(pucEncData->C,s_SDF_RevBuf + Offset,uiDataLength - 2 - 97);
	pucEncData->L = uiDataLength - 2 - 97;
	return SDR_OK;
}
int SDF_ExternalDecrypt_ECC(	
	void* hSessionHandle,
	unsigned int uiAlgID,
	ECCrefPrivateKey *pucPrivateKey,
	ECCCipher *pucEncData,
	unsigned char *pucData,
	unsigned int *puiDataLength)
{
	uint32_t Offset;
	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if(!pucEncData || !pucData|| !pucPrivateKey)
	{
		return SDR_INARGERR;
	}
	if(uiAlgID != SGD_SM2)
	{
		return SDR_INARGERR;
	}
	if(pucPrivateKey->bits != ECC_BIT_LEN)
	{
		return SDR_INARGERR;
	}
	CLA = cla_securify;
	INS = ins_asy_dec;
	P1 = 0x01;
	P2 = 0x02;
	P3 = 0x00;
	Offset = 2;
	//私钥+04+c1c3c2
	memmove(DATA_BUF + Offset,pucPrivateKey->K,ECC_BIT_LEN/8);
	Offset +=ECC_BIT_LEN/8;
	DATA_BUF[Offset++]=0x04;
	memmove(DATA_BUF + Offset,pucEncData->x,ECC_BIT_LEN/8);
	Offset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + Offset,pucEncData->y,ECC_BIT_LEN/8);
	Offset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + Offset,pucEncData->M,ECC_BIT_LEN/8);
	Offset +=ECC_BIT_LEN/8;
	memmove(DATA_BUF + Offset,pucEncData->C,pucEncData->L);
	Offset += pucEncData->L;

	Offset -=2;

	DATA_BUF[0] = (Offset>>8)&0xFF;
	DATA_BUF[1] = Offset&0xFF;

	if(Driver_Transfer(s_SDF_SendBuf, 7 + Offset, s_SDF_RevBuf,puiDataLength))
	{
		return SDR_PKOPERR;
	}
	if(s_SDF_RevBuf[*puiDataLength - 2] != 0x90 ||s_SDF_RevBuf[*puiDataLength - 1]  != 0x00)
	{
		return SDR_PKOPERR;
	}
	*puiDataLength -=2;
	memmove(pucData,s_SDF_RevBuf,*puiDataLength);
	return SDR_OK;
}

int SDF_InternalEncrypt_ECC(
	void *hSessionHandle,
	unsigned int uiIPKIndex,
	unsigned int uiAlgID,
	unsigned char *pucData,
	unsigned int uiDataLength,
	ECCCipher *pucEncData)
{
	return SDR_OK;
}
int SDF_InternalDecrypt_ECC(
	void *hSessionHandle,
	unsigned int uiISKIndex,
	unsigned int uiAlgID,
	ECCCipher *pucEncData,
	unsigned char *pucData,
	unsigned int *uiDataLength)
{
	return SDR_OK;
}

int SDF_Encrypt(
	void *hSessionHandle,
	void *hKeyHandle,
	unsigned int uiAlgID,
	unsigned char *pucIV,
	unsigned char *pucData,
	unsigned int uiDataLength,
	unsigned char *pucEncData,
	unsigned int *puiEncDataLength)
{
	uint16_t kid,offset;
	uint8_t ucIv[16],dup_data[503];
	

	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if(!pucEncData || !pucData || !hKeyHandle)
	{
		return SDR_INARGERR;
	}
	if (!puiEncDataLength)
	{
		return SDR_INARGERR;
	}
	if(uiAlgID != SGD_SM4_ECB && uiAlgID != SGD_SM4_CBC)
	{
		return SDR_INARGERR;
	}
	memset(ucIv,0x00,16);
	memset(dup_data,0x00,503);
	//导入密钥
	CLA = cla_securify;
	INS = ins_sy_import;
	P1 = 0x00;
	P2 = 0x00;
	P3 = SMS4_KEY_LENGTH + 2;
	kid=0x0012; 
	DATA_BUF[0] = (kid>>8)&0xFF;
	DATA_BUF[1] = kid&0xFF;
	memmove(DATA_BUF + 2,hKeyHandle,SMS4_KEY_LENGTH);

	if(Driver_Transfer(s_SDF_SendBuf, 5 + SMS4_KEY_LENGTH + 2, s_SDF_RevBuf,puiEncDataLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[0] != 0x90 ||s_SDF_RevBuf[1] != 0x00)
	{
		return SDR_SYMOPERR;
	}
	//密钥初始化
	CLA = cla_securify;
	INS = ins_sy_operate;
	P1 = 0x00;//init 0 
	P2 = 0x01;//enc
	P3 = 0x00;
	offset = 2;
	DATA_BUF[offset++] = 0x00;//sm4
	if(uiAlgID == SGD_SM4_ECB)
	{
		DATA_BUF[offset++] = 0x00;//ecb
	}
	else
	{
		DATA_BUF[offset++] = 0x01;//cbc
		memmove(ucIv,pucIV,16);
	}
	DATA_BUF[offset++] = 0x00;//128bit
	DATA_BUF[offset++] = 0x80;
	DATA_BUF[offset++] = (kid>>8)&0xFF;//kid
	DATA_BUF[offset++] = kid&0xFF;
	memmove(DATA_BUF + offset, ucIv,16);
	offset -=2; 
	offset +=16;
	DATA_BUF[0] = (offset>>8)&0xFF;
	DATA_BUF[1] = offset&0xFF;
	if(Driver_Transfer(s_SDF_SendBuf, 7 + offset, s_SDF_RevBuf,puiEncDataLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[0] != 0x90 ||s_SDF_RevBuf[1] != 0x00)
	{
		return SDR_SYMOPERR;
	}
	//加密
	CLA = cla_securify;
	INS = ins_sy_operate;
	P1 = 0x01;//init 0 
	P2 = 0x01;//enc
	P3 = 0xFF;

	memmove(DATA_BUF + 4,dup_data, 503);
	memmove(DATA_BUF + 4 + 503,pucData,uiDataLength);
	//uiDataLength += 503;
	DATA_BUF[0] = (uiDataLength>>24)&0xFF;
	DATA_BUF[1] = (uiDataLength>>16)&0xFF;
	DATA_BUF[2] = (uiDataLength>>8)&0xFF;
	DATA_BUF[3] = uiDataLength&0xFF;
	uiDataLength += 503;
	if(Driver_Transfer(s_SDF_SendBuf, 9 + uiDataLength, s_SDF_RevBuf,&uiDataLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[uiDataLength - 2] != 0x90 ||s_SDF_RevBuf[uiDataLength - 1] != 0x00)
	{
		return SDR_SYMOPERR;
	}
	memmove(pucEncData,s_SDF_RevBuf+506,uiDataLength-506 - 2);
	*puiEncDataLength = uiDataLength - 506 - 2;
	return SDR_OK;
}

int SDF_Decrypt(
	void *hSessionHandle,
	void *hKeyHandle,
	unsigned int uiAlgID,
	unsigned char *pucIV,
	unsigned char *pucEncData,
	unsigned int uiEncDataLength,
	unsigned char *pucData,
	unsigned int *puiDataLength)
{
	uint16_t kid,offset;
	uint8_t ucIv[16],dup_data[503];
	

	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if(!pucEncData || !pucData ||!hKeyHandle)
	{
		return SDR_INARGERR;
	}
	if (!puiDataLength)
	{
		return SDR_INARGERR;
	}
	if(uiAlgID != SGD_SM4_ECB && uiAlgID != SGD_SM4_CBC)
	{
		return SDR_INARGERR;
	}
	memset(ucIv,0x00,16);
	memset(dup_data,0x00,503);
	//导入密钥
	CLA = cla_securify;
	INS = ins_sy_import;
	P1 = 0x00;
	P2 = 0x00;//dec
	P3 = SMS4_KEY_LENGTH + 2;
	kid=0x0012; 
	DATA_BUF[0] = (kid>>8)&0xFF;
	DATA_BUF[1] = kid&0xFF;
	memmove(DATA_BUF + 2,hKeyHandle,SMS4_KEY_LENGTH);

	if(Driver_Transfer(s_SDF_SendBuf, 5 + SMS4_KEY_LENGTH + 2, s_SDF_RevBuf,puiDataLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[0] != 0x90 ||s_SDF_RevBuf[1] != 0x00)
	{
		return SDR_SYMOPERR;
	}
	//密钥初始化
	CLA = cla_securify;
	INS = ins_sy_operate;
	P1 = 0x00;//init 0 
	P2 = 0x00;//dec
	P3 = 0x00;
	offset = 2;
	DATA_BUF[offset++] = 0x00;//sm4
	if(uiAlgID == SGD_SM4_ECB)
	{
		DATA_BUF[offset++] = 0x00;//ecb
	}
	else
	{
		DATA_BUF[offset++] = 0x01;//cbc
		memmove(ucIv,pucIV,16);
	}
	DATA_BUF[offset++] = 0x00;//128bit
	DATA_BUF[offset++] = 0x80;
	DATA_BUF[offset++] = (kid>>8)&0xFF;//kid
	DATA_BUF[offset++] = kid&0xFF;
	memmove(DATA_BUF + offset, ucIv,16);
	offset -=2; 
	offset +=16;
	DATA_BUF[0] = (offset>>8)&0xFF;
	DATA_BUF[1] = offset&0xFF;
	if(Driver_Transfer(s_SDF_SendBuf, 7 + offset, s_SDF_RevBuf,puiDataLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[0] != 0x90 ||s_SDF_RevBuf[1] != 0x00)
	{
		return SDR_SYMOPERR;
	}
	//解密
	CLA = cla_securify;
	INS = ins_sy_operate;
	P1 = 0x01;//update 0 
	P2 = 0x00;//dec
	P3 = 0xFF;

	memmove(DATA_BUF + 4,dup_data, 503);
	memmove(DATA_BUF + 4 + 503,pucEncData,uiEncDataLength);
	DATA_BUF[0] = (uiEncDataLength>>24)&0xFF;
	DATA_BUF[1] = (uiEncDataLength>>16)&0xFF;
	DATA_BUF[2] = (uiEncDataLength>>8)&0xFF;
	DATA_BUF[3] = uiEncDataLength&0xFF;
	uiEncDataLength += 503;
	if(Driver_Transfer(s_SDF_SendBuf, 9 + uiEncDataLength, s_SDF_RevBuf,&uiEncDataLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[uiEncDataLength - 2] != 0x90 ||s_SDF_RevBuf[uiEncDataLength - 1] != 0x00)
	{
		return SDR_SYMOPERR;
	}
	memmove(pucData,s_SDF_RevBuf+506,uiEncDataLength-506 - 2);
	*puiDataLength = uiEncDataLength - 506 - 2;

	return SDR_OK;
}

int SDF_CalculateMAC(
	void *hSessionHandle,
	void *hKeyHandle,
	unsigned int uiAlgID,
	unsigned char *pucIV,
	unsigned char *pucData,
	unsigned int uiDataLength,
	unsigned char *pucMAC,
	unsigned int *puiMACLength)
{
	if (!puiMACLength)
		return SDR_INARGERR;
	*puiMACLength = 16; /* CBC-MAC length */
	return SDR_OK;
}

int SDF_HashInit(
	void *hSessionHandle,
	unsigned int uiAlgID,
	ECCrefPublicKey *pucPublicKey,
	unsigned char *pucID,
	unsigned int uiIDLength)
{

	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if(uiAlgID != SGD_SM3 && uiAlgID != SGD_SHA256)
	{
		return SDR_INARGERR;
	}
	CLA = cla_securify;
	INS = ins_hash;
	P1 = 0x00;
	if(uiAlgID == SGD_SM3)
	{
		P2 = 0x02;
	}
	else
	{
		P2 = 0x00;
	}
	hash_type = P2;
	P3 = 0x00;
	if(Driver_Transfer(s_SDF_SendBuf, 5, s_SDF_RevBuf,&uiAlgID))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[uiAlgID - 2 ] != 0x90 ||s_SDF_RevBuf[uiAlgID - 1] != 0x00)
	{
		return SDR_STEPERR;
	}

	return SDR_OK;
}

int SDF_HashUpdate(
	void *hSessionHandle,
	unsigned char *pucData,
	unsigned int uiDataLength)
{

	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	CLA = cla_securify;
	INS = ins_hash;
	P1 = 0x01;
	P2 = hash_type;
	P3 = 0x00;
	DATA_BUF[0] = (uiDataLength>>8)&0xFF;
	DATA_BUF[1] = uiDataLength&0xFF;
	memmove(DATA_BUF + 2,pucData,uiDataLength);
	if(Driver_Transfer(s_SDF_SendBuf,7+uiDataLength, s_SDF_RevBuf,&uiDataLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[uiDataLength - 2 ] != 0x90 ||s_SDF_RevBuf[uiDataLength - 1] != 0x00)
	{
		return SDR_STEPERR;
	}
	return SDR_OK;
}

int SDF_HashFinal(void *hSessionHandle,
	unsigned char *pucHash,
	unsigned int *puiHashLength)
{

	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if (!puiHashLength)
	{
		return SDR_INARGERR;
	}
	CLA = cla_securify;
	INS = ins_hash;
	P1 = 0x02;
	P2 = hash_type;
	P3 = 0x00;
	if(Driver_Transfer(s_SDF_SendBuf,5, s_SDF_RevBuf,puiHashLength))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[*puiHashLength - 2] != 0x90 ||s_SDF_RevBuf[*puiHashLength - 1] != 0x00)
	{
		return SDR_STEPERR;
	}
	*puiHashLength =32;
	memcpy(pucHash,s_SDF_RevBuf,*puiHashLength);
	return SDR_OK;
}

int SDF_CreateFile(
	void *hSessionHandle,
	unsigned char *pucFileName,
	unsigned int uiNameLen,
	unsigned int uiFileSize)
{
	uint8_t offset;
	SDF_TRACE();
	if(!hSessionHandle)
	{
		return SDR_OPENSESSION;
	}
	if (!pucFileName)
	{
		return SDR_INARGERR;
	}
	CLA = cla_securify;
	INS = ins_create_ef;
	P1 = 0x00;
	P2 = 0x00;
	offset = 0x00;
	DATA_BUF[offset++]=0xA0;
	DATA_BUF[offset++]=0x01;
	DATA_BUF[offset++] = (uiFileSize>>8)&0xFF;
	DATA_BUF[offset++] = uiFileSize&0xFF;
	DATA_BUF[offset++] = 0x28;
	memmove(DATA_BUF+offset,pucFileName,uiNameLen);
	P3 = (offset+uiNameLen)&0xFF;
	if(Driver_Transfer(s_SDF_SendBuf,5+offset+uiNameLen, s_SDF_RevBuf,&uiFileSize))
	{
		return SDR_SYMOPERR;
	}
	if(s_SDF_RevBuf[0] != 0x90 ||s_SDF_RevBuf[1] != 0x00)
	{
		return SDR_STEPERR;
	}
	return SDR_OK;
}

int SDF_ReadFile(
	void *hSessionHandle,
	unsigned char *pucFileName,
	unsigned int uiNameLen,
	unsigned int uiOffset,
	unsigned int *puiReadLength,
	unsigned char *pucBuffer)
{
	if (!puiReadLength)
		return SDR_INARGERR;
	return SDR_OK;
}

int SDF_WriteFile(
	void *hSessionHandle,
	unsigned char *pucFileName,
	unsigned int uiNameLen,
	unsigned int uiOffset,
	unsigned int uiWriteLength,
	unsigned char *pucBuffer)
{
	return SDR_OK;
}

int SDF_DeleteFile(
	void *hSessionHandle,
	unsigned char *pucFileName,
	unsigned int uiNameLen)
{
	return SDR_OK;
}


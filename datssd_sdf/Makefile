
CC= $(CROSS_COMPILE)gcc
CPP= $(CROSS_COMPILE)g++
CFLAGS= -Wall -O3 -g -fPIC 
CPPFLAGS= -Wall -O3 -g -fPIC 
LDFLAGS += -shared -fPIC -lpthread -lm -lrt -lstdc++  -L 

CSRCS= $(wildcard ./*.c) 
CPPSRCS=$(wildcard ./*.cpp)
SHLIBS=libsdf.so
DRIVERLIBS=libdrive.so

COBJS := $(CSRCS:%.c=%.o)  
CPPOBJS := $(CPPSRCS:%.cpp=%.o)  


all: $(SHLIBS)
$(COBJS) : %.o: %.c  
	$(CC) $(CFLAGS) -c $< -o $@   
$(SHLIBS): $(COBJS) 
	$(CC)  -shared -o $(SHLIBS) $(COBJS)  
	sudo cp $(SHLIBS) /usr/local/lib/engines-1.1/
	sudo cp ../apps/gmssl /usr/local/bin/
#	cp  $(SHLIBS) ../apps/ 
	sudo make -C ../
	sudo make install_engines -C ../
	sudo make install_dev  -C ../
# all:$(SHLIBS) $(DRIVERLIBS)
# $(COBJS) : %.o: %.c  
# 	$(CC) $(CFLAGS) -c $< -o $@   
# $(CPPOBJS) : %.o: %.cpp  
# 	$(CPP) $(CPPFLAGS) -c $< -o $@   
# $(DRIVERLIBS): $(CPPOBJS)  
# 	$(CC)  -shared -o $(DRIVERLIBS) $(CPPOBJS)
# $(SHLIBS): $(COBJS) 
# 	$(CC)  -shared -o $(SHLIBS) $(COBJS) $(LDFLAGS) $(DRIVERLIBS)   
# 	cp  $(SHLIBS) ../apps/ 

clean:
	rm -f $(COBJS)
#	rm -f $(CPPOBJS)
	rm -f *.so
	rm -f *.d

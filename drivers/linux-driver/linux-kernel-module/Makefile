ARCH:=riscv
CROSS_COMPILE:=riscv64-unknown-linux-gnu-

ROOTDIR:=./linux-noelv/5.10.25-r0/linux-5.10.25-headers/usr/src/linux-headers-5.10.25
MAKEARCH:=$(MAKE) ARCH=$(ARCH) CROSS_COMPILE=$(CROSS_COMPILE)

obj-m += lkm_safesu.o

all:
	$(MAKEARCH) -C $(ROOTDIR) M=${shell pwd} modules
#	$(CROSS_COMPILE)gcc test_lkm_safesu.c -o test_lkm_safesu

clean:
	$(MAKEARCH) -C $(ROOTDIR) M=${shell pwd} clean

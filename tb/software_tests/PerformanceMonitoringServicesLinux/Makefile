ARCH:=riscv
CROSS_COMPILE:=riscv64-unknown-linux-gnu-
CC=$(CROSS_COMPILE)gcc

obj-m += lkm_safesu.o

main: main.c lib
	$(CC) main.c ubs.c -pthread -lm -o test -L./ -l:linux_safesu_hw.a

lib: 
	$(CC) ./../../../drivers/linux-driver/linux_safesu_hw.c -c -o linux_safesu_hw.a

clean:
	rm *.a

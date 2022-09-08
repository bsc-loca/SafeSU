myMulticore_c_src = \
	myMulticore_main.c \
	syscalls.c \
	PMU.c \

myMulticore_riscv_src = \
	crt.S 

myMulticore_c_objs			= $(patsubst %.c, %.o, $(myMulticore_c_src))
myMulticore_riscv_objs = $(patsubst %.S, %.o, $(myMulticore_riscv_src))

myMulticore_host_bin = myMulticore.host 
$(myMulticore_host_bin): $(myMulticore_c_src)
	$(HOST_COMP) $^ -o $(myMulticore_host_bin)

myMulticore_riscv_bin = myMulticore.riscv 
$(myMulticore_riscv_bin): $(myMulticore_c_objs) $(myMulticore_riscv_objs)
	$(RISCV_LINK) $(myMulticore_c_objs) $(myMulticore_riscv_objs) -o $(myMulticore_riscv_bin) $(RISCV_LINK_OPTS)

junk += $(myMulticore_c_objs) $(myMulticore_riscv_objs) $(myMulticore_host_bin) $(myMulticore_riscv_bin)


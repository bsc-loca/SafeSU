UART ?=1
XLEN ?=64
cores_number=6

default: all setup

src_dir=source

#--------------------------------------------------------------------
# Experiment parameters SafeSU(ONLY MODIFY THESE VALUES)
#--------------------------------------------------------------------
__TEST_ITERATIONS__ ?= 8
__TEST_MATRIX_ROW__ ?= 50
__TEST_MATRIX_COL__ ?= 50


setup:
	@echo "ITERATIONS ARE $(__CORE0_UBENCH_NAME__)"
	@echo "CONTENDER UBENCH IS $(__CONTENDER_NAME__)"


#--------------------------------------------------------------------
# Sources
#--------------------------------------------------------------------
bmarks := safesu_example
bmarks_riscv=$(addsuffix .riscv,  $(bmarks))

#--------------------------------------------------------------------
# Build rules
#--------------------------------------------------------------------
incs  += -I./drivers/uart -I./env -I./common -I./../../../drivers/6-core-256e -I./../../../drivers/plic  -$(addprefix I , $(src_dir)/$(bmarks))

RISCV_PREFIX ?= /mnt/caos_hw/Programs/ncc-1.0.4-gcc/bin/riscv-gaisler-elf-
RISCV_GCC ?= $(RISCV_PREFIX)gcc
RISCV_GCC_OPTS ?= -DPREALLOCATE=1 -mcmodel=medany -static -std=gnu99  -fno-inline-small-functions -ffast-math -fno-common -fno-builtin-printf -march=rv64ima -mabi=lp64 -DNO_UART_WAIT=$(UART) -DNOSTAT
RISCV_LINK ?= $(RISCV_GCC) $(incs) #-T ./common/test.ld $(incs)
RISCV_LINK_OPTS ?= $(incs) -static -nostdlib -nostartfiles -lm -lgcc

define compile_template
$(1).riscv: $(wildcard $(1)/*) $(wildcard ./common/*) $(wildcard ./drivers/uart/*)  $(wildcard ./env/*)
	mkdir -p $$@  
	if [ "$(cores_number)" -ge "1" ]; then \
	$$(RISCV_GCC) $$(incs) $$(RISCV_GCC_OPTS) -D__TEST_ITERATIONS__=$(__TEST_ITERATIONS__) -D__TEST_MATRIX_ROW__=$(__TEST_MATRIX_ROW__)  -D__TEST_MATRIX_COL__=$(__TEST_MATRIX_COL__)  $$(EXTRA_GCC_OPTS) -o $$@/$(1)-1.riscv $(wildcard $(src_dir)/$(1)/*.c)  $(wildcard ./common/*.c) $(wildcard ./drivers/uart/*.c) $(wildcard ./../../../drivers/6-core-256e/*.c) $(wildcard ./../../../drivers/plic/*.c) $(wildcard ./common/*.S) $$(RISCV_LINK_OPTS) -T ./common/noelv1.ld; \
	fi
	if [ "$(cores_number)" -ge "2" ]; then \
	$$(RISCV_GCC) $$(incs) $$(RISCV_GCC_OPTS) -D__TEST_ITERATIONS__=$(__TEST_ITERATIONS__) -D__TEST_MATRIX_ROW__=$(__TEST_MATRIX_ROW__)  -D__TEST_MATRIX_COL__=$(__TEST_MATRIX_COL__)  $$(EXTRA_GCC_OPTS) -o $$@/$(1)-2.riscv $(wildcard $(src_dir)/$(1)/*.c)  $(wildcard ./common/*.c) $(wildcard ./drivers/uart/*.c) $(wildcard ./../../../drivers/6-core-256e/*.c) $(wildcard ./../../../drivers/plic/*.c) $(wildcard ./common/*.S) $$(RISCV_LINK_OPTS) -T ./common/noelv2.ld; \
	fi
	if [ "$(cores_number)" -ge "3" ]; then \
	$$(RISCV_GCC) $$(incs) $$(RISCV_GCC_OPTS) -D__TEST_ITERATIONS__=$(__TEST_ITERATIONS__) -D__TEST_MATRIX_ROW__=$(__TEST_MATRIX_ROW__)  -D__TEST_MATRIX_COL__=$(__TEST_MATRIX_COL__)  $$(EXTRA_GCC_OPTS) -o $$@/$(1)-3.riscv $(wildcard $(src_dir)/$(1)/*.c)  $(wildcard ./common/*.c) $(wildcard ./drivers/uart/*.c) $(wildcard ./../../../drivers/6-core-256e/*.c) $(wildcard ./../../../drivers/plic/*.c) $(wildcard ./common/*.S) $$(RISCV_LINK_OPTS) -T ./common/noelv3.ld; \
	fi
	if [ "$(cores_number)" -ge "4" ]; then \
	$$(RISCV_GCC) $$(incs) $$(RISCV_GCC_OPTS) -D__TEST_ITERATIONS__=$(__TEST_ITERATIONS__) -D__TEST_MATRIX_ROW__=$(__TEST_MATRIX_ROW__)  -D__TEST_MATRIX_COL__=$(__TEST_MATRIX_COL__)  $$(EXTRA_GCC_OPTS) -o $$@/$(1)-4.riscv $(wildcard $(src_dir)/$(1)/*.c)  $(wildcard ./common/*.c) $(wildcard ./drivers/uart/*.c) $(wildcard ./../../../drivers/6-core-256e/*.c) $(wildcard ./../../../drivers/plic/*.c) $(wildcard ./common/*.S) $$(RISCV_LINK_OPTS) -T ./common/noelv4.ld; \
	fi
	if [ "$(cores_number)" -ge "5" ]; then \
	$$(RISCV_GCC) $$(incs) $$(RISCV_GCC_OPTS) -D__TEST_ITERATIONS__=$(__TEST_ITERATIONS__) -D__TEST_MATRIX_ROW__=$(__TEST_MATRIX_ROW__)  -D__TEST_MATRIX_COL__=$(__TEST_MATRIX_COL__)  $$(EXTRA_GCC_OPTS) -o $$@/$(1)-5.riscv $(wildcard $(src_dir)/$(1)/*.c) $(wildcard ./common/*.c) $(wildcard ./drivers/uart/*.c) $(wildcard ./../../../drivers/6-core-256e/*.c) $(wildcard ./../../../drivers/plic/*.c) $(wildcard ./common/*.S) $$(RISCV_LINK_OPTS) -T ./common/noelv5.ld; \
	fi
	if [ "$(cores_number)" -ge "6" ]; then \
	$$(RISCV_GCC) $$(incs) $$(RISCV_GCC_OPTS) -D__TEST_ITERATIONS__=$(__TEST_ITERATIONS__) -D__TEST_MATRIX_ROW__=$(__TEST_MATRIX_ROW__)  -D__TEST_MATRIX_COL__=$(__TEST_MATRIX_COL__)  $$(EXTRA_GCC_OPTS) -o $$@/$(1)-6.riscv $(wildcard $(src_dir)/$(1)/*.c) $(wildcard ./common/*.c) $(wildcard ./drivers/uart/*.c) $(wildcard ./../../../drivers/6-core-256e/*.c) $(wildcard ./../../../drivers/plic/*.c) $(wildcard ./common/*.S) $$(RISCV_LINK_OPTS) -T ./common/noelv6.ld; \
	fi

endef

$(foreach bmark,$(bmarks),$(eval $(call compile_template,$(bmark))))


#------------------------------------------------------------
# Default

all: $(bmarks_riscv)

#------------------------------------------------------------
# Clean up

clean:
	rm -rf *.riscv vivado*

prefix          := /usr/local
abs_top_src_dir := /home/bscuser/GITLAB/multicore_pmu/lagarto-lowrisc/lagarto_modulos/AXI_PMU/tb/software_tests/multicore_sample_program
instbasedir     := $(DESTDIR)$(prefix)
bmarkdir        := $(abs_top_src_dir)/programs
isa_src_dir     := $(abs_top_src_dir)/isa

all: programs isa

install: all
	install -p -m 644 *.hex $(instbasedir)/share/riscv-tests

programs:
	$(MAKE) -f $(bmarkdir)/Makefile bmarkdir=$(bmarkdir)

isa:
	$(MAKE) -f $(isa_src_dir)/Makefile isa_src_dir=$(isa_src_dir)

.PHONY: programs isa

#set dependencies
cd ../../../../
. dep.sh
# make project
cd vsim
make clean
make sim-lagarto
# make our test
cd $TOP/lagarto_modulos/AXI_PMU/tb/software_tests/pmu_sample_program/programs
make clean
make
cp myWrite.riscv.hex $TOP/vsim 
cd -
#get waveform
./DefaultConfig-sim +vcd +vcd_name=write_test.vcd +max-cycles=10000  +load=./myWrite.riscv.hex | spike-dasm > write_test.log
#display waveform
gtkwave write_test.vcd gtkwave_configs/io_debug_PC_OP_FUNC_CLK_AXIMEM_AXIIO.gtkw

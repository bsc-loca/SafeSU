#set dependencies
cd ../../../../
. dep.sh
# make project
cd vsim
make clean
make sim-lagarto
#Copy most recent drivers
cp $TOP/fpga/board/kc705/driver/PMU.c  $TOP/lagarto_modulos/AXI_PMU/tb/software_tests/pmu_sample_program/programs/common/ 
cp $TOP/fpga/board/kc705/driver/PMU.h  $TOP/lagarto_modulos/AXI_PMU/tb/software_tests/pmu_sample_program/programs/common/ 
cp $TOP/fpga/board/kc705/driver/PMU.o  $TOP/lagarto_modulos/AXI_PMU/tb/software_tests/pmu_sample_program/programs/ 
# make our test
cd $TOP/lagarto_modulos/AXI_PMU/tb/software_tests/pmu_sample_program/programs
make clean
make
cp myWrite.riscv.hex $TOP/vsim 
cd -
#get waveform
./DefaultConfig-sim +vcd +vcd_name=write_test.vcd +max-cycles=10000  +load=./myWrite.riscv.hex | spike-dasm > write_test.log
#display waveform
gtkwave write_test.vcd $TOP/lagarto_modulos/AXI_PMU/tb/verilator/testSOC.gtkw

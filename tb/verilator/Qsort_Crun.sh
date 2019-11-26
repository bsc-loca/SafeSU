#set dependencies
cd ../../../../
. dep.sh
# make project
cd vsim
#Copy most recent drivers
cp $TOP/fpga/board/kc705/driver/PMU.c  $TOP/lagarto_modulos/AXI_PMU/tb/software_tests/multicore_pmu_qsort/programs/common/ 
cp $TOP/fpga/board/kc705/driver/PMU.h  $TOP/lagarto_modulos/AXI_PMU/tb/software_tests/multicore_pmu_qsort/programs/common/ 
# make our test
cd $TOP/lagarto_modulos/AXI_PMU/tb/software_tests/multicore_pmu_qsort/programs
make clean
make
cp qsort.riscv.hex $TOP/vsim/qsort.riscv.hex 
cd -
#get waveform
./DefaultConfig-sim +vcd +vcd_name=qsort100.vcd +max-cycles=30000 +load=./qsort.riscv.hex | spike-dasm > write_test.log
#display waveform
gtkwave qsort100.vcd $TOP/lagarto_modulos/AXI_PMU/tb/verilator/testSOC.gtkw

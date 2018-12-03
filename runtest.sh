RED='\033[0;31m'
NC='\033[0m' # No Color

echo -e "${RED} Modify the script if you need to set your verilator path ${NC}"
#____________start set path verilator
#export TOP=/home/bscuser/BSC/lowrisc
#export VERILATOR_ROOT=$TOP/verilator
#____________end set path verilator
rm -rf obj_dir 
#verilator -Wall --cc --trace AXI_PMU.sv  ../mux_4to1/mux_4to1.sv ../demux_4to1/demux_4to1_n.sv ../mux_4to1_n/mux_4to1_n.sv --exe AXI_PMU_TB.cpp -CFLAGS "-std=c++14"
verilator -Wall --cc --trace AXI_PMU.v --exe AXI_PMU_TB.cpp -CFLAGS "-std=c++14"

cd obj_dir/
make -f VAXI_PMU.mk 
./VAXI_PMU
gtkwave VAXI_PMU.vcd  ../tests.gtkw

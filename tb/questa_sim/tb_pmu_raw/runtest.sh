#$1
TOP=../../..
RED='\033[7;31m'
NC='\033[0m' # No Color
      
vlib PMU_raw
vmap work $PWD/PMU_raw
vlog +acc=rn +incdir+$TOP/hdl/ $TOP/hdl/PMU_raw.sv $TOP/submodules/MCCU/hdl/* $TOP/submodules/crossbar/hdl/*.sv $TOP/submodules/RDC/hdl/*.sv $TOP/submodules/overflow/*.sv $TOP/submodules/quota/*.sv  $TOP/submodules/counters/*.sv  tb_PMU_raw.sv ./colors.vh $TOP/submodules/seu_ip/*.sv
vmake PMU_raw/ > Makefile

if [ -z "$1" ]
then
      printf "${RED}WARNING: Check if you want Fault Tolerance active or not${RED}${NC}\n"
      printf "${RED}To enable FT add -gFT=1 after vsim${RED}${NC}\n"
      vsim work.tb_PMU_raw -do "view wave -new" -do "do wave.do" -do "run -all"
else
      echo "#INFO# Test Default IP "
      vsim -gFT=0 work.tb_PMU_raw $1 -do "do save_wave.do"
      echo "#INFO# Test FT IP"
      vsim -gFT=1 work.tb_PMU_raw $1 -do "do save_wave.do"
fi

#$1
TOP=../../../
RED='\033[7;31m'
NC='\033[0m' # No Color
if [ -z "$1" ]
then
      vlib MCCU
      vmap work $PWD/MCCU
      vlog +acc=rn +incdir+$TOP/hdl/ $TOP/hdl/*.sv $TOP/submodules/MCCU/hdl/MCCU.sv $TOP/submodules/seu_ip/way3*.sv tb_MCCU.sv
      vmake MCCU/ > Makefile
      printf "${RED}WARNING: Check if you want Fault Tolerance active or not${RED}${NC}\n"
      printf "${RED}To enable FT add -gFT=1 after vsim${RED}${NC}\n"
      vsim work.tb_MCCU -do "view wave -new" -do "do wave.do" -do "run -all"
else
      vlib MCCU
      vmap work $PWD/MCCU
      vlog +acc=rn +incdir+$TOP/hdl/ $TOP/hdl/*.sv $TOP/submodules/MCCU/hdl/MCCU.sv $TOP/submodules/seu_ip/way3*.sv tb_MCCU.sv
      vmake MCCU/ > Makefile
      echo "#INFO# Test Default IP "
      vsim -gFT=0 work.tb_MCCU $1 -do "do save_wave.do"
      echo "#INFO# Test FT IP"
      vsim -gFT=1 work.tb_MCCU $1 -do "do save_wave.do"
fi

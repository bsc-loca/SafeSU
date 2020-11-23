#$1
TOP=../../..
      
vlib PMU_raw
vmap work $PWD/PMU_raw
vlog +acc=rn +incdir+$TOP/hdl/ $TOP/hdl/PMU_raw.sv $TOP/submodules/MCCU/hdl/* $TOP/submodules/crossbar/hdl/*.sv $TOP/submodules/RDC/hdl/*.sv $TOP/submodules/overflow/*.sv $TOP/submodules/quota/*.sv  $TOP/submodules/counters/*.sv  tb_PMU_raw.sv ./colors.vh
vmake PMU_raw/ > Makefile

if [ -z "$1" ]
then
      vsim work.tb_PMU_raw -do "view wave -new" -do "do wave.do" -do "run -all"
else
      vsim work.tb_PMU_raw $1 -do "do save_wave.do"
fi

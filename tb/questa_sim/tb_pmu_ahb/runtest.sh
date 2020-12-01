#$1
TOP=../../..
      
vlib pmu_ahb
vmap work $PWD/pmu_ahb
vlog +acc=rn +incdir+$TOP/hdl/ $TOP/hdl/pmu_ahb.sv $TOP/hdl/PMU_raw.sv $TOP/submodules/MCCU/hdl/* $TOP/submodules/crossbar/hdl/*.sv $TOP/submodules/RDC/hdl/*.sv $TOP/submodules/overflow/*.sv $TOP/submodules/quota/*.sv  $TOP/submodules/counters/*.sv  tb_pmu_ahb.sv ./colors.vh
vmake pmu_ahb/ > Makefile

if [ -z "$1" ]
then
      vsim work.tb_pmu_ahb -do "view wave -new" -do "do wave.do" -do "run -all"
else
      vsim work.tb_pmu_ahb $1 -do "do save_wave.do"
fi

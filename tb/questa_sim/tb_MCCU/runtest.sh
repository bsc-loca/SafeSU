#$1
TOP=../../../
if [ -z "$1" ]
then
      vlib MCCU
      vmap work $PWD/MCCU
      vlog +acc=rn +incdir+$TOP/hdl/ $TOP/hdl/*.sv $TOP/submodules/seu_ip/way3*.sv tb_MCCU.sv
      vmake MCCU/ > Makefile
      vsim work.tb_MCCU -do "view wave -new" -do "do wave.do" -do "run -all"
else
      vlib MCCU
      vmap work $PWD/MCCU
      vlog +acc=rn +incdir+$TOP/hdl/ $TOP/hdl/*.sv $TOP/submodules/seu_ip/way3*.sv tb_MCCU.sv
      vmake MCCU/ > Makefile
      vsim work.tb_MCCU $1 -do "do save_wave.do"
fi

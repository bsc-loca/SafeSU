$1

if [ -z "$1" ]
then
      vlib MCCU
      vmap work $PWD/MCCU
      vlog +acc=rn +incdir+../../hdl/ ../../hdl/*.sv tb_MCCU.sv
      vmake MCCU/ > Makefile
      vsim work.tb_MCCU -do "view wave -new" -do "do wave.do" -do "run 40000"
else
      vlib MCCU
      vmap work $PWD/MCCU
      vlog +acc=rn +incdir+../../hdl/ ../../hdl/*.sv tb_MCCU.sv
      vmake MCCU/ > Makefile
      vsim work.tb_MCCU $1 -do "run 40000"
fi

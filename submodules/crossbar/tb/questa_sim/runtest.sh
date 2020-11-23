#$1

if [ -z "$1" ]
then
      vlib crossbar
      vmap work $PWD/crossbar
      vlog +acc=rn +incdir+../../hdl/ ../../hdl/*.sv tb_crossbar.sv
      vmake crossbar/ > Makefile
      vsim work.tb_crossbar -do "view wave -new" -do "do wave.do" -do "run -all"
else
      vlib crossbar
      vmap work $PWD/crossbar
      vlog +acc=rn +incdir+../../hdl/ ../../hdl/*.sv tb_crossbar.sv
      vmake crossbar/ > Makefile
      vsim work.tb_crossbar $1 -do "do save_wave.do"
fi

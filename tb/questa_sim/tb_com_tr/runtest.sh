# Use ./runtest.sh -batch to run the simulation in batch mode
TOP=../../..
      
vlib com_tr
vmap work $PWD/com_tr
vlog +acc=rn +incdir+$TOP/hdl/ $TOP/submodules/seu_ip/com_tr.sv  tb_com_tr.sv ./colors.vh
vmake com_tr/ > Makefile

if [ -z "$1" ]
then
      vsim work.tb_com_tr -do "do wave.do" -do "run -all"
else
      vsim work.tb_com_tr $1 -do "do save_wave.do"
fi

# Use ./runtest.sh -batch to run the simulation in batch mode
TOP=../../..
      
vlib reg_sbf
vmap work $PWD/reg_sbf
vlog +acc=rn +incdir+$TOP/hdl/ $TOP/submodules/seu_ip/reg_sbf.sv  tb_reg_sbf.sv ./colors.vh
vmake reg_sbf/ > Makefile

if [ -z "$1" ]
then
      vsim work.tb_reg_sbf -do "do wave.do" -do "run -all"
else
      vsim work.tb_reg_sbf $1 -do "do save_wave.do"
fi

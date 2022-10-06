# Use ./runtest.sh -batch to run the simulation in batch mode
TOP=../../..
      
vlib hamming16t11d
vmap work $PWD/hamming16t11d
vlog +acc=rn +incdir+$TOP/hdl/ $TOP/submodules/seu_ip/hamming16t11d_dec.sv $TOP/submodules/seu_ip/hamming16t11d_enc.sv  tb_hamming16t11d.sv ./colors.vh
vmake hamming16t11d/ > Makefile

if [ -z "$1" ]
then
      vsim work.tb_hamming16t11d -do "do wave.do" -do "run -all"
else
      vsim work.tb_hamming16t11d $1 -do "do save_wave.do"
fi

# Use ./runtest.sh -batch to run the simulation in batch mode
TOP=../../..
      
vlib hamming32t26d
vmap work $PWD/hamming32t26d
vlog +acc=rn +incdir+$TOP/hdl/ $TOP/submodules/seu_ip/hamming32t26d_dec.sv $TOP/submodules/seu_ip/hamming32t26d_enc.sv  tb_hamming32t26d.sv ./colors.vh
vmake hamming32t26d/ > Makefile

if [ -z "$1" ]
then
      vsim work.tb_hamming32t26d -do "do wave.do" -do "run -all"
else
      vsim work.tb_hamming32t26d $1 -do "do save_wave.do"
fi

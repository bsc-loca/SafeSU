CYCLES=-all
TOP=../../..
mv /AXI_PMU /tmp 2>/dev/null
vlib AXI_PMU
vmap work $PWD/AXI_PMU
vlog +acc=rn +incdir+$TOP/hdl/ $TOP/hdl/*.sv $TOP/submodules/MCCU/hdl/* $TOP/submodules/RDC/hdl/*.sv  ./fifos/hdl/sync_fifo.v ./axi_test_master/hdl/axi_test_master.v tb_AXI_PMU.sv ./colors.vh
vmake AXI_PMU/ > Makefile
if [ -z "$1" ]
then
      vsim work.tb_AXI_PMU -do "view wave -new" -do "do wave.do" -do "run $CYCLES"
else
      vsim work.tb_AXI_PMU $1 -do "run $CYCLES"
fi

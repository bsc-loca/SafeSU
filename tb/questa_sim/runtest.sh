$1
CYCLES=1800000
mv /AXI_PMU /tmp
vlib AXI_PMU
vmap work $PWD/AXI_PMU
vlog +acc=rn +incdir+../../hdl/ ../../hdl/*.sv ../../submodules/MCCU/hdl/* ./fifos/hdl/sync_fifo.v ./axi_test_master/hdl/axi_test_master.v tb_AXI_PMU.sv ./colors.vh
vmake AXI_PMU/ > Makefile
if [ -z "$1" ]
then
      vsim work.tb_AXI_PMU -do "view wave -new" -do "do wave.do" -do "run $CYCLES"
else
      vsim work.tb_AXI_PMU $1 -do "run $CYCLES"
fi

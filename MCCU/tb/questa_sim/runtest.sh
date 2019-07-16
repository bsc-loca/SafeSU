vlib MCCU
vmap work $PWD/MCCU
vlog +incdir+../../hdl/ ../../hdl/*.sv tb_MCCU.v
vmake MCCU/ > Makefile
vsim work.tb_MCCU

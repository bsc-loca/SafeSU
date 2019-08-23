#Check that the formal properties pass
sby -f MCCU.sby
#gtkwave ./MCCU/engine_0/trace.vcd MCCU.gtkw
#Run a particular case
#sby -f MCCU_cover.sby
#Show the trace of the cover
gtkwave ./MCCU/engine_0/trace.vcd MCCU.gtkw

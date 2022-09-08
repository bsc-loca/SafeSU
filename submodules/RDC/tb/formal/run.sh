#Check that the formal properties pass
sby -f RDC.sby
#gtkwave ./RDC/engine_0/trace.vcd RDC.gtkw
#Run a particular case
#sby -f RDC_cover.sby
#Show the trace of the cover
gtkwave ./RDC/engine_0/trace.vcd RDC.gtkw

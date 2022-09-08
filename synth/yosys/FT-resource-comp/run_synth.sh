echo "Starting synth "
echo "Area for FreePDK45 is reported in square micrometers"
echo "0/6 runs done"
yosys -D D4  yosys_45.ys > ./logs/synth_D4.log &
yosys -D D8  yosys_45.ys > ./logs/synth_D8.log &
yosys -D D11  yosys_45.ys > ./logs/synth_D11.log &
yosys -D D16  yosys_45.ys > ./logs/synth_D16.log 
wait
echo "4/6 runs done"
yosys -D D32  yosys_45.ys > ./logs/synth_D32.log &
yosys -D D64  yosys_45.ys > ./logs/synth_D64.log 
wait
echo "1/1 runs done"
echo "Done! Reporting area & cycle time"
cd logs
ack "netlist of module"\|"Delay"\|"area"
cd ..

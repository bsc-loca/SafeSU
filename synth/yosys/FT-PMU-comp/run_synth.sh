echo "Starting synth "
echo "Area for FreePDK45 is reported in square micrometers"
echo "0/2 runs done"
yosys yosys_45_nft.ys > ./logs/synth_NFT.log &
yosys yosys_45_ft.ys > ./logs/synth_FT.log 
echo "2/2 runs done"
echo "Done! Reporting area & cycle time"
cd logs
ack "netlist of module"\|"Delay"\|"area"
cd ..

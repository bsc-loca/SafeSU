set sdc_version 1.4

# Set the current design
current_design top_ft
#get_ports: ports that are in the top module
#set_case_analysis 0 [get_ports tck]
create_clock -name "clk" -add -period 1 [get_ports clk_i] 

set_clock_groups -name grp4 -asynchronous -group {clk} 

set_input_delay  -clock [get_clocks clk] -add_delay 0.1 [all_inputs]
set_output_delay -clock [get_clocks clk] -add_delay 0.1 [all_outputs]

set_max_fanout 15 [current_design]

set_load 0.5 [all_outputs]
set_input_transition 0.2 [all_inputs]

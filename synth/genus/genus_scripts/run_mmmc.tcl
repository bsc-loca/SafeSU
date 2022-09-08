#### Template Script for RTL->Gate-Level Flow  
#### MMMC Flow
set TOP_FILE "top_ft"
set SDC_SETTING "./Constraints/top_nft_65.sdc"
source "./genus_scripts/run_mmmc_test.tcl"

####################################################################
## Create outputs directories
####################################################################

if {![file exists ${_LOG_PATH}]} {
  file mkdir ${_LOG_PATH}
  puts "Creating directory ${_LOG_PATH}"
}

if {![file exists ${_OUTPUTS_PATH}]} {
  file mkdir ${_OUTPUTS_PATH}
  puts "Creating directory ${_OUTPUTS_PATH}"
}

if {![file exists ${_REPORTS_PATH}]} {
  file mkdir ${_REPORTS_PATH}
  puts "Creating directory ${_REPORTS_PATH}"
}


###################################################################################
## Define cost groups (clock-clock, clock-output, input-clock, input-output)
###################################################################################

## Uncomment to remove already existing costgroups before creating new ones.
## rm [vfind /designs/* -cost_group *]

if {[llength [all::all_seqs]] > 0} { 
  define_cost_group -name I2C -design $DESIGN
  define_cost_group -name C2O -design $DESIGN
  define_cost_group -name C2C -design $DESIGN
  path_group -from [all::all_seqs] -to [all::all_seqs] -group C2C -name C2Cs -view view_slow
  path_group -from [all::all_seqs] -to [all::all_seqs] -group C2C -name C2Cf -view view_fast
  path_group -from [all::all_seqs] -to [all::all_seqs] -group C2C -name C2Ct -view view_typ

  path_group -from [all::all_seqs] -to [all_outputs] -group C2O -name C2Os -view view_slow
  path_group -from [all::all_seqs] -to [all_outputs] -group C2O -name C2Of -view view_fast
  path_group -from [all::all_seqs] -to [all_outputs] -group C2O -name C2Ot -view view_typ

  path_group -from [all_inputs]  -to [all::all_seqs] -group I2C -name I2Cs -view view_slow
  path_group -from [all_inputs]  -to [all::all_seqs] -group I2C -name I2Cf -view view_fast
  path_group -from [all_inputs]  -to [all::all_seqs] -group I2C -name I2Ct -view view_typ
}

define_cost_group -name I2O -design $DESIGN
path_group -from [all_inputs]  -to [all_outputs] -group I2O -name I2Os -view view_slow
path_group -from [all_inputs]  -to [all_outputs] -group I2O -name I2Of -view view_fast
path_group -from [all_inputs]  -to [all_outputs] -group I2O -name I2Ot -view view_typ

foreach cg [vfind / -cost_group *] {
  report timing -cost_group [list $cg] >> $_REPORTS_PATH/${DESIGN}_pretim.rpt
}

# Retime in the whole design
set_db / .control_logic_optimization advanced
#set_db "design:${DESIGN}" .retime true
#set_db [get_db modules *fpuv_wrapper*] .retime true
#set_db [get_db modules *LoadBuffer*] .retime true

#### To turn off sequential merging on the design 
#### uncomment & use the following attributes.
##set_db / .optimize_merge_flops false 
##set_db / .optimize_merge_latches false 
#### For a particular instance use attribute 'optimize_merge_seqs' to turn off sequential merging. 

#truncate the names to a maximun of 255 characteres before starting with the synthesis
update_names -max_length 255 -module

####################################################################################################
## Synthesizing to generic 
####################################################################################################
set_db [vfind /des* -design ${DESIGN}] .undesirable_libcells {SD* SE*}
#TODO: retime prepare causes an error, that possibly causes that retime is not possible. this is related with negedege clock usage in jtag and dbr
#retime -prepare
set_db / .syn_generic_effort high
syn_generic
puts "Runtime & Memory after 'syn_generic'"
time_info GENERIC

report_dp > $_REPORTS_PATH/generic/${DESIGN}_datapath.rpt
write_snapshot -directory $_REPORTS_PATH -tag generic
report_summary -directory $_REPORTS_PATH


####################################################################################################
## Synthesizing to gates
####################################################################################################
set_db [vfind /des* -design ${DESIGN}] .dft_dont_scan true
set_db [vfind /des* -design ${DESIGN}] .undesirable_libcells {SD* SE*}
set_db / .syn_map_effort high 
syn_map 
puts "Runtime & Memory after 'syn_map'"
time_info MAPPED
write_snapshot -directory $_REPORTS_PATH -tag map
report_dp > $_REPORTS_PATH/map/${DESIGN}_datapath.rpt


foreach cg [vfind / -cost_group *] {
  report_timing -cost_group [list $cg] > $_REPORTS_PATH/${DESIGN}_[vbasename $cg]_post_map.rpt
}


write_do_lec -revised_design fv_map -logfile ${_LOG_PATH}/rtl2intermediate.lec.log > ${_OUTPUTS_PATH}/rtl2intermediate.lec.do

## ungroup -threshold <value>


#######################################################################################################
## Incremental Synthesis
#######################################################################################################

## Uncomment to remove assigns & insert tiehilo cells during Incremental synthesis
##set_db / .remove_assigns true 
##set_remove_assign_options -buffer_or_inverter <libcell> -design <design|subdesign> 
##set_db / .use_tiehilo_for_const <none|duplicate|unique>  
 
set_db [vfind /des* -design ${DESIGN}] .undesirable_libcells {SD* SE*}
set_db / .syn_opt_effort high 
syn_opt 
puts "Runtime & Memory after syn_opt"
time_info INCREMENTAL


foreach cg [vfind / -cost_group *] {
  report_timing -cost_group [list $cg] > $_REPORTS_PATH/${DESIGN}_[vbasename $cg]_post_opt.rpt
}


######################################################################################################
## write Innovus file set (verilog, SDC, config, etc.)
######################################################################################################


report_dp > $_REPORTS_PATH/${DESIGN}_datapath_incr.rpt
report_messages > $_REPORTS_PATH/${DESIGN}_messages.rpt
write_snapshot -directory ${_REPORTS_PATH} -tag final -innovus ${DESIGN}
write_db -to_file ${_OUTPUTS_PATH}/${DESIGN}.db
report_summary -directory $_REPORTS_PATH
write_design -innovus  -base_name ${_OUTPUTS_PATH}/${DESIGN}_syn ${DESIGN}
write_sdf -design ${DESIGN}  > ${_OUTPUTS_PATH}/${DESIGN}_slow.sdf
#write_hdl  > ${_OUTPUTS_PATH}/${DESIGN}_netlist.v
#write_script > ${_OUTPUTS_PATH}/${DESIGN}_m.script
write_hdl -pg > ${_OUTPUTS_PATH}/${DESIGN}_netlist_pg.v

report_messages > $_REPORTS_PATH/${DESIGN}_messages.rpt

## write_hdl  > ${_OUTPUTS_PATH}/${DESIGN}_m.v
#write_sdc > ${_OUTPUTS_PATH}/${DESIGN}_m.sdc


#################################
### write_do_lec
#################################


write_do_lec -golden_design ${_OUTPUTS_PATH}/${DESIGN}_intermediate.v -revised_design ${_OUTPUTS_PATH}/${DESIGN}_m.v -logfile  ${_LOG_PATH}/intermediate2final.lec.log > ${_OUTPUTS_PATH}/intermediate2final.lec.do
##Uncomment if the RTL is to be compared with the final netlist..
##write_do_lec -revised_design ${_OUTPUTS_PATH}/${DESIGN}_m.v -logfile ${_LOG_PATH}/rtl2final.lec.log > ${_OUTPUTS_PATH}/rtl2final.lec.do

puts "Final Runtime & Memory."
time_info FINAL
puts "============================"
puts "Synthesis Finished ........."
puts "============================"

file copy [get_db / .stdout_log ] ${_LOG_PATH}/.

exit

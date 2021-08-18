#### Template Script for RTL->Gate-Level Flow
#### MMMC Flow


if {[file exists /proc/cpuinfo]} {
  sh grep "model name" /proc/cpuinfo
  sh grep "cpu MHz"    /proc/cpuinfo
}

puts "Hostname : [info hostname]"

##############################################################################
## Preset global variables and attributes
##############################################################################
set original_argv $argv
set argv [list $TOP_FILE]
source "set_variables.tcl"
set argv $original_argv
set DESIGN $TOP_MODULE
set LIB_PATH /eda/lib_65nm
set DATE [clock format [clock seconds] -format "%b%d-%T"]
set _OUTPUTS_PATH ${build}/tsmc_${NUM_TRACKS}_outputs
set _REPORTS_PATH ${build}/tsmc_${NUM_TRACKS}_reports
set _LOG_PATH ${build}/tsmc_${NUM_TRACKS}_logs


#Remove parameters names to obtain shorter names
set_db hdl_parameter_naming_style ""

##set ET_WORKDIR <ET work directory>
# Search library paths
if { $NUM_TRACKS eq {10tracks}} {
	set_db / .init_lib_search_path {  \
		/eda/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/tcbn65lphpbwp-set/tcbn65lphpbwp_200a_FE/TSMCHOME/digital/Back_End/lef/tcbn65lphpbwp_140a/lef/ \
    /eda/libs/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/TSMCHOME_LVT_SEF/digital/Back_End/lef/tcbn65lphpbwplvt_140a/lef/ \
	}
} elseif { $NUM_TRACKS eq {7tracks}} {
	set_db / .init_lib_search_path {  \
		/eda/lib_65nm/TSMC/65/CMOS/LP/stclib/7-track/tcbn65lpbwp7t-set/tcbn65lpbwp7t_220a_FE/TSMCHOME/digital/Back_End/lef/tcbn65lpbwp7t_141a/lef/ \
	}
} else {
	puts "No valid NUM_TRACKS variable"
	exit
}

set_db / .script_search_path {.}

##For design size of 1.5M - 5M gates, use 8 to 16 CPUs. For designs > 5M gates, use 16 to 32 CPUs
set_db / .max_cpus_per_server 8
#set_db / .super_thread_servers {batch}
#set_db / .super_thread_batch_command \
#    {qsub -hard -N GenusST3 -q cadence@bosin1cl  -b y -j y -pe make2 16 -o /dev/null}
#set_db / .super_thread_kill_command {qdel}
#set_db / .st_launch_wait_time 4


##Default undriven/unconnected setting is 'none'
set_db / .hdl_unconnected_input_port_value 0
set_db / .hdl_undriven_output_port_value   0
set_db / .hdl_undriven_signal_value        0


##set_db / .wireload_mode <value>
set_db / .information_level 9

###############################################################
## Library setup
###############################################################

# MMMMC Flow
if {$NUM_TRACKS eq {10tracks}} {
    read_mmmc -design $DESIGN ${scripts}/mmmc10t.tcl
## PLE
read_physical -lef  { \
	tcbn65lphpbwp_9lmT2.lef \
  tcbn65lphpbwplvt_9lmT2.lef \
 }
} elseif {$NUM_TRACKS eq {7tracks}} {
read_mmmc -design $DESIGN ${scripts}/mmmc7t.tcl
## PLE
read_physical -lef  { \
	tcbn65lpbwp7t_9lmT2.lef \
 }
} else {
	puts "No valid NUM_TRACKS variable"
	exit
}


##generates <signal>_reg[<bit_width>] format
set_db / .hdl_array_naming_style %s\[%d\]

## Turn on TNS, affects global and incr opto
#set_db / .tns_opto true

####################################################################
## Load Design
####################################################################

##source verilog_files.tcl
read_hdl -sv -f ${build}/src_file_sv
elaborate $DESIGN
puts "Runtime & Memory after 'read_hdl'"
time_info Elaboration

init_design

check_design -unresolved
#check_design

####################################################################
## Constraints Setup
####################################################################

#puts "The number of exceptions is [llength [find /designs/$DESIGN -exception *]]"

#set_db / .force_wireload <wireload name> "/designs/$DESIGN"
report timing -lint -verbose

puts "******** END OF ELABORATION PHASE **********"

################################################################################
#
# Genus(TM) Synthesis Solution setup file
# Created by Genus(TM) Synthesis Solution 19.11-s087_1
#   on 08/20/2021 13:29:10
#
# This file can only be run in Genus Common UI mode.
#
################################################################################


# This script is intended for use with Genus(TM) Synthesis Solution version 19.11-s087_1


# Remove Existing Design
################################################################################
if {[::legacy::find -design design:top_ft] ne ""} {
  puts "** A design with the same name is already loaded. It will be removed. **"
  delete_obj design:top_ft
}


# To allow user-readonly attributes
################################################################################
::legacy::set_attribute -quiet force_tui_is_remote 1 /


# Source INIT Setup file
################################################################################
source /users/gcabo/genus_runs_pmu/bsc_pmu_ft750/synth/genus/genus_build/tsmc_10tracks_reports/final_top_ft.genus_init.tcl
read_metric -id current /users/gcabo/genus_runs_pmu/bsc_pmu_ft750/synth/genus/genus_build/tsmc_10tracks_reports/final_top_ft.metrics.json

phys::read_script /users/gcabo/genus_runs_pmu/bsc_pmu_ft750/synth/genus/genus_build/tsmc_10tracks_reports/final_top_ft.g.gz
puts "\n** Restoration Completed **\n"


# Data Integrity Check
################################################################################
# program version
if {"[string_representation [::legacy::get_attribute program_version /]]" != "19.11-s087_1"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-91] "golden program_version: 19.11-s087_1  current program_version: [string_representation [::legacy::get_attribute program_version /]]"
}
# license
if {"[string_representation [::legacy::get_attribute startup_license /]]" != "Genus_Synthesis"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-91] "golden license: Genus_Synthesis  current license: [string_representation [::legacy::get_attribute startup_license /]]"
}
# slack
set _slk_ [::legacy::get_attribute slack design:top_ft]
if {[regexp {^-?[0-9.]+$} $_slk_]} {
  set _slk_ [format %.1f $_slk_]
}
if {$_slk_ != "-574.6"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden slack: -574.6,  current slack: $_slk_"
}
unset _slk_
# multi-mode slack
if {"[string_representation [::legacy::get_attribute slack_by_mode design:top_ft]]" != "{{mode:top_ft/view_typ 153.1} {mode:top_ft/view_slow -574.6} {mode:top_ft/view_superslow -536.0} {mode:top_ft/view_fast 479.5}}"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden slack_by_mode: {{mode:top_ft/view_typ 153.1} {mode:top_ft/view_slow -574.6} {mode:top_ft/view_superslow -536.0} {mode:top_ft/view_fast 479.5}}  current slack_by_mode: [string_representation [::legacy::get_attribute slack_by_mode design:top_ft]]"
}
# tns
set _tns_ [::legacy::get_attribute tns design:top_ft]
if {[regexp {^-?[0-9.]+$} $_tns_]} {
  set _tns_ [format %.0f $_tns_]
}
if {$_tns_ != "181413"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden tns: 181413,  current tns: $_tns_"
}
unset _tns_
# cell area
set _cell_area_ [::legacy::get_attribute cell_area design:top_ft]
if {[regexp {^-?[0-9.]+$} $_cell_area_]} {
  set _cell_area_ [format %.0f $_cell_area_]
}
if {$_cell_area_ != "204206"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden cell area: 204206,  current cell area: $_cell_area_"
}
unset _cell_area_
# net area
set _net_area_ [::legacy::get_attribute net_area design:top_ft]
if {[regexp {^-?[0-9.]+$} $_net_area_]} {
  set _net_area_ [format %.0f $_net_area_]
}
if {$_net_area_ != "78401"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden net area: 78401,  current net area: $_net_area_"
}
unset _net_area_
# library domain count
if {[llength [::legacy::find /libraries -library_domain *]] != "4"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden # library domains: 4  current # library domains: [llength [::legacy::find /libraries -library_domain *]]"
}

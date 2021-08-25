################################################################################
#
# Genus(TM) Synthesis Solution setup file
# Created by Genus(TM) Synthesis Solution 19.11-s087_1
#   on 08/20/2021 11:36:04
#
# This file can only be run in Genus Common UI mode.
#
################################################################################


# This script is intended for use with Genus(TM) Synthesis Solution version 19.11-s087_1


# Remove Existing Design
################################################################################
if {[::legacy::find -design design:top_nft] ne ""} {
  puts "** A design with the same name is already loaded. It will be removed. **"
  delete_obj design:top_nft
}


# To allow user-readonly attributes
################################################################################
::legacy::set_attribute -quiet force_tui_is_remote 1 /


# Source INIT Setup file
################################################################################
source /users/gcabo/genus_runs_pmu/bsc_pmu_nft750/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.genus_init.tcl
read_metric -id current /users/gcabo/genus_runs_pmu/bsc_pmu_nft750/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.metrics.json

phys::read_script /users/gcabo/genus_runs_pmu/bsc_pmu_nft750/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.g.gz
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
set _slk_ [::legacy::get_attribute slack design:top_nft]
if {[regexp {^-?[0-9.]+$} $_slk_]} {
  set _slk_ [format %.1f $_slk_]
}
if {$_slk_ != "-215.0"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden slack: -215.0,  current slack: $_slk_"
}
unset _slk_
# multi-mode slack
if {"[string_representation [::legacy::get_attribute slack_by_mode design:top_nft]]" != "{{mode:top_nft/view_typ 399.2} {mode:top_nft/view_slow -182.9} {mode:top_nft/view_superslow -215.0} {mode:top_nft/view_fast 637.5}}"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden slack_by_mode: {{mode:top_nft/view_typ 399.2} {mode:top_nft/view_slow -182.9} {mode:top_nft/view_superslow -215.0} {mode:top_nft/view_fast 637.5}}  current slack_by_mode: [string_representation [::legacy::get_attribute slack_by_mode design:top_nft]]"
}
# tns
set _tns_ [::legacy::get_attribute tns design:top_nft]
if {[regexp {^-?[0-9.]+$} $_tns_]} {
  set _tns_ [format %.0f $_tns_]
}
if {$_tns_ != "7105"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden tns: 7105,  current tns: $_tns_"
}
unset _tns_
# cell area
set _cell_area_ [::legacy::get_attribute cell_area design:top_nft]
if {[regexp {^-?[0-9.]+$} $_cell_area_]} {
  set _cell_area_ [format %.0f $_cell_area_]
}
if {$_cell_area_ != "75582"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden cell area: 75582,  current cell area: $_cell_area_"
}
unset _cell_area_
# net area
set _net_area_ [::legacy::get_attribute net_area design:top_nft]
if {[regexp {^-?[0-9.]+$} $_net_area_]} {
  set _net_area_ [format %.0f $_net_area_]
}
if {$_net_area_ != "30782"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden net area: 30782,  current net area: $_net_area_"
}
unset _net_area_
# library domain count
if {[llength [::legacy::find /libraries -library_domain *]] != "4"} {
   mesg_send [::legacy::find -message /messages/PHYS/PHYS-92] "golden # library domains: 4  current # library domains: [llength [::legacy::find /libraries -library_domain *]]"
}

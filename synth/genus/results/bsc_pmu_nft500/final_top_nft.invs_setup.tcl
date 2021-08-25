################################################################################
#
# Innovus setup file
# Created by Genus(TM) Synthesis Solution 19.11-s087_1
#   on 08/20/2021 10:48:59
#
################################################################################
#
# Genus(TM) Synthesis Solution setup file
# This file can only be run in Innovus Common UI mode.
#
################################################################################

      set _t0 [clock seconds]
      puts [format  {%%%s Begin Genus to Innovus Setup (%s)} \# [clock format $_t0 -format {%m/%d %H:%M:%S}]]
    
if {[is_attribute -obj_type root read_physical_allow_multiple_port_pin_without_must_join]} {
  set_db read_physical_allow_multiple_port_pin_without_must_join true
} else {
  set read_physical_allow_multiple_port_pin_without_must_join 1
}


# Design Import
################################################################################
set_library_unit -cap 1pf -time 1ns
## Reading FlowKit settings file
source /users/gcabo/genus_runs_pmu/bsc_pmu_nft500/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.flowkit_settings.tcl

source /users/gcabo/genus_runs_pmu/bsc_pmu_nft500/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.invs_init.tcl

# Reading metrics file
################################################################################
read_metric -id current /users/gcabo/genus_runs_pmu/bsc_pmu_nft500/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.metrics.json

## Reading common preserve file for dont_touch and dont_use preserve settings
source /users/gcabo/genus_runs_pmu/bsc_pmu_nft500/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.preserve.tcl



# Mode Setup
################################################################################
source /users/gcabo/genus_runs_pmu/bsc_pmu_nft500/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.mode

# Source cell padding from Genus
################################################################################
source /users/gcabo/genus_runs_pmu/bsc_pmu_nft500/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.cell_pad.tcl 


# Reading write_name_mapping file
################################################################################
if {[is_attribute -obj_type port original_name] && [is_attribute -obj_type pin original_name] && [is_attribute -obj_type pin is_phase_inverted]} {
  source /users/gcabo/genus_runs_pmu/bsc_pmu_nft500/synth/genus/genus_build/tsmc_10tracks_reports/final_top_nft.wnm_attrs.tcl
}

eval_legacy { set edi_pe::pegConsiderMacroLayersUnblocked 1 }
eval_legacy { set edi_pe::pegPreRouteWireWidthBasedDensityCalModel 1 }

      set _t1 [clock seconds]
      puts [format  {%%%s End Genus to Innovus Setup (%s, real=%s)} \# [clock format $_t1 -format {%m/%d %H:%M:%S}] [clock format [expr {28800 + $_t1 - $_t0}] -format {%H:%M:%S}]]
    

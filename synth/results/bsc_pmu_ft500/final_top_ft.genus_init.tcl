################################################################################
#
# Init setup file
# Created by Genus(TM) Synthesis Solution on 08/20/2021 12:05:57
#
################################################################################

      if { ![is_common_ui_mode] } {
        error "This script must be loaded into an 'innovus -stylus' session."
      }
    


read_mmmc /users/gcabo/genus_runs_pmu/bsc_pmu_ft500/synth/genus/genus_build/tsmc_10tracks_reports/final_top_ft.mmmc.tcl

read_physical -lef {/eda/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/tcbn65lphpbwp-set/tcbn65lphpbwp_200a_FE/TSMCHOME/digital/Back_End/lef/tcbn65lphpbwp_140a/lef//tcbn65lphpbwp_9lmT2.lef /eda/libs/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/TSMCHOME_LVT_SEF/digital/Back_End/lef/tcbn65lphpbwplvt_140a/lef//tcbn65lphpbwplvt_9lmT2.lef}

read_netlist /users/gcabo/genus_runs_pmu/bsc_pmu_ft500/synth/genus/genus_build/tsmc_10tracks_reports/final_top_ft.v.gz

init_design -skip_sdc_read

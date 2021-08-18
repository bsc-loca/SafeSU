#################################################################################
#
# Created by Genus(TM) Synthesis Solution 19.11-s087_1 on Tue Aug 17 16:57:50 CEST 2021
#
#################################################################################

## library_sets
create_library_set -name typ_25C \
    -timing { /eda/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/tcbn65lphpbwp-set/tcbn65lphpbwp_200a_FE/TSMCHOME/digital/Front_End/timing_power_noise/NLDM/tcbn65lphpbwp_140a/tcbn65lphpbwptc.lib \
              /eda/libs/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/TSMCHOME_LVT_NLDM/digital/Front_End/timing_power_noise/NLDM/tcbn65lphpbwplvt_140a/tcbn65lphpbwplvttc.lib }
create_library_set -name ss_125C \
    -timing { /eda/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/tcbn65lphpbwp-set/tcbn65lphpbwp_200a_FE/TSMCHOME/digital/Front_End/timing_power_noise/NLDM/tcbn65lphpbwp_140a/tcbn65lphpbwpwc.lib \
              /eda/libs/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/TSMCHOME_LVT_NLDM/digital/Front_End/timing_power_noise/NLDM/tcbn65lphpbwplvt_140a/tcbn65lphpbwplvtwc.lib }
create_library_set -name ff_0C \
    -timing { /eda/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/tcbn65lphpbwp-set/tcbn65lphpbwp_200a_FE/TSMCHOME/digital/Front_End/timing_power_noise/NLDM/tcbn65lphpbwp_140a/tcbn65lphpbwpbc.lib \
              /eda/libs/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/TSMCHOME_LVT_NLDM/digital/Front_End/timing_power_noise/NLDM/tcbn65lphpbwplvt_140a/tcbn65lphpbwplvtbc.lib }

## opcond
create_opcond -name op_cond_typ -voltage 1.2 -temperature 25.0
create_opcond -name op_cond_slow -voltage 1.08 -temperature 125.0
create_opcond -name op_cond_fast -voltage 1.32 -temperature 0.0

## timing_condition
create_timing_condition -name timing_cond_typ \
    -opcond op_cond_typ \
    -library_sets { typ_25C }
create_timing_condition -name timing_cond_slow \
    -opcond op_cond_slow \
    -library_sets { ss_125C }
create_timing_condition -name timing_cond_fast \
    -opcond op_cond_fast \
    -library_sets { ff_0C }

## rc_corner
create_rc_corner -name _default_rc_corner \
    -cap_table /eda/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/tcbn65lphpbwp-set/tcbn65lphpbwp_200a_FE/TSMCHOME/digital/Back_End/lef/tcbn65lphpbwp_140a/techfiles/captable/cln65lp_1p09m+alrdl_top2_typical.captable \
    -pre_route_res 1.0 \
    -pre_route_cap 1.0 \
    -pre_route_clock_res 0.0 \
    -pre_route_clock_cap 0.0 \
    -post_route_res {1.0 1.0 1.0} \
    -post_route_cap {1.0 1.0 1.0} \
    -post_route_cross_cap {1.0 1.0 1.0} \
    -post_route_clock_res {1.0 1.0 1.0} \
    -post_route_clock_cap {1.0 1.0 1.0}
create_rc_corner -name _rcworst_rc_corner \
    -cap_table /eda/lib_65nm/TSMC/65/CMOS/LP/stclib/10-track/tcbn65lphpbwp-set/tcbn65lphpbwp_200a_FE/TSMCHOME/digital/Back_End/lef/tcbn65lphpbwp_140a/techfiles/captable/cln65lp_1p09m+alrdl_top2_rcworst.captable \
    -pre_route_res 1.0 \
    -pre_route_cap 1.0 \
    -pre_route_clock_res 0.0 \
    -pre_route_clock_cap 0.0 \
    -post_route_res {1.0 1.0 1.0} \
    -post_route_cap {1.0 1.0 1.0} \
    -post_route_cross_cap {1.0 1.0 1.0} \
    -post_route_clock_res {1.0 1.0 1.0} \
    -post_route_clock_cap {1.0 1.0 1.0}

## delay_corner
create_delay_corner -name delay_corner_typ \
    -early_timing_condition { timing_cond_typ } \
    -late_timing_condition { timing_cond_typ } \
    -early_rc_corner _default_rc_corner \
    -late_rc_corner _default_rc_corner
create_delay_corner -name delay_corner_slow \
    -early_timing_condition { timing_cond_slow } \
    -late_timing_condition { timing_cond_slow } \
    -early_rc_corner _default_rc_corner \
    -late_rc_corner _default_rc_corner
create_delay_corner -name delay_corner_superslow \
    -early_timing_condition { timing_cond_slow } \
    -late_timing_condition { timing_cond_slow } \
    -early_rc_corner _rcworst_rc_corner \
    -late_rc_corner _rcworst_rc_corner
create_delay_corner -name delay_corner_fast \
    -early_timing_condition { timing_cond_fast } \
    -late_timing_condition { timing_cond_fast } \
    -early_rc_corner _default_rc_corner \
    -late_rc_corner _default_rc_corner

## constraint_mode
create_constraint_mode -name _default_constraint_mode_ \
    -sdc_files { /users/gcabo/bsc_pmu/synth/genus/genus_build/tsmc_10tracks_reports/final_top._default_constraint_mode_.sdc }

## analysis_view
create_analysis_view -name view_typ \
    -constraint_mode _default_constraint_mode_ \
    -delay_corner delay_corner_typ
create_analysis_view -name view_slow \
    -constraint_mode _default_constraint_mode_ \
    -delay_corner delay_corner_slow
create_analysis_view -name view_superslow \
    -constraint_mode _default_constraint_mode_ \
    -delay_corner delay_corner_superslow
create_analysis_view -name view_fast \
    -constraint_mode _default_constraint_mode_ \
    -delay_corner delay_corner_fast

## set_analysis_view
set_analysis_view -setup { view_typ view_slow view_superslow view_fast } \
                  -hold { view_typ view_slow view_superslow view_fast }

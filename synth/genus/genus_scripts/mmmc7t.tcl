## Usage
# Pass one  Sdc file name within Constraints folder 
# top_ft_65.sdc  top_nft_65.sdc
#####
# Library sets
##########
#set LIB_PATH /eda/lib_65nm
create_library_set -name typ_25C -timing {\
/eda/lib_65nm/TSMC/65nm/CMOS/LP/stclib/7-track/TSMCHOME/digital/Front_End/timing_power_noise/NLDM/tcbn65lpbwp7t_141a/tcbn65lpbwp7ttc.lib \
}
create_library_set -name ss_125C -timing {\
/eda/lib_65nm/TSMC/65nm/CMOS/LP/stclib/7-track/TSMCHOME/digital/Front_End/timing_power_noise/NLDM/tcbn65lpbwp7t_141a/tcbn65lpbwp7twc.lib \
}
create_library_set -name ff_0C -timing {\
/eda/lib_65nm/TSMC/65nm/CMOS/LP/stclib/7-track/TSMCHOME/digital/Front_End/timing_power_noise/NLDM/tcbn65lpbwp7t_141a/tcbn65lpbwp7tbc.lib \
}

####
# opcond
####
create_opcond -name op_cond_typ -voltage 1.2 -temperature 25
create_opcond -name op_cond_slow -voltage 1.08 -temperature 125
create_opcond -name op_cond_fast -voltage 1.32 -temperature 0

####
# timing_cond
####
create_timing_condition -name timing_cond_typ -opcond op_cond_typ -library_sets {typ_25C}
create_timing_condition -name timing_cond_slow -opcond op_cond_slow -library_sets {ss_125C}
create_timing_condition -name timing_cond_fast -opcond op_cond_fast -library_sets {ff_0C}

####
# RC corner
####
create_rc_corner -name _default_rc_corner -cap_table \
/eda/lib_65nm/TSMC/65nm/CMOS/LP/stclib/7-track/TSMCHOME/digital/Back_End/lef/tcbn65lpbwp7t_141a/techfiles/captable/cln65lp_1p09m+alrdl_top2_typical.captable

####
# Delay corner
####
create_delay_corner -name delay_corner_typ -timing_condition timing_cond_typ \
-rc_corner _default_rc_corner  
create_delay_corner -name delay_corner_slow -timing_condition timing_cond_slow \
-rc_corner _default_rc_corner  
create_delay_corner -name delay_corner_fast -timing_condition timing_cond_fast \
-rc_corner _default_rc_corner  

####
# Constraints
####
create_constraint_mode -name _default_constraint_mode_ -sdc_files $SDC_SETTING
 
####
# Analysis views
####
create_analysis_view -name view_typ  -constraint_mode _default_constraint_mode_ \
-delay_corner delay_corner_typ
create_analysis_view -name view_slow  -constraint_mode _default_constraint_mode_ \
-delay_corner delay_corner_slow
create_analysis_view -name view_fast  -constraint_mode _default_constraint_mode_ \
-delay_corner delay_corner_fast
 
 
set_analysis_view -setup {view_typ view_slow view_fast}
# -hold option is not supported by Genus

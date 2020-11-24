onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix ascii /tb_PMU_raw/tb_test_name
add wave -noupdate /tb_PMU_raw/dut_PMU_raw/rstn_i
add wave -noupdate /tb_PMU_raw/dut_PMU_raw/regs_i
add wave -noupdate /tb_PMU_raw/dut_PMU_raw/regs_o
add wave -noupdate /tb_PMU_raw/dut_PMU_raw/clk_i
add wave -noupdate {/tb_PMU_raw/dut_PMU_raw/crossbar_cfg[0]}
add wave -noupdate {/tb_PMU_raw/dut_PMU_raw/crossbar_cfg[1]}
add wave -noupdate {/tb_PMU_raw/dut_PMU_raw/crossbar_cfg[2]}
add wave -noupdate {/tb_PMU_raw/dut_PMU_raw/crossbar_cfg[3]}
add wave -noupdate {/tb_PMU_raw/dut_PMU_raw/crossbar_cfg[4]}
add wave -noupdate {/tb_PMU_raw/dut_PMU_raw/crossbar_cfg[5]}
add wave -noupdate {/tb_PMU_raw/dut_PMU_raw/crossbar_cfg[6]}
add wave -noupdate {/tb_PMU_raw/dut_PMU_raw/crossbar_cfg[7]}
add wave -noupdate -color Coral {/tb_PMU_raw/dut_PMU_raw/unpacked_cbi_int[0]}
add wave -noupdate -color Coral {/tb_PMU_raw/dut_PMU_raw/unpacked_cbi_int[1]}
add wave -noupdate -color Coral {/tb_PMU_raw/dut_PMU_raw/unpacked_cbi_int[2]}
add wave -noupdate -color Coral {/tb_PMU_raw/dut_PMU_raw/unpacked_cbi_int[3]}
add wave -noupdate -color Coral {/tb_PMU_raw/dut_PMU_raw/unpacked_cbi_int[4]}
add wave -noupdate -color Coral {/tb_PMU_raw/dut_PMU_raw/unpacked_cbi_int[5]}
add wave -noupdate -color Coral {/tb_PMU_raw/dut_PMU_raw/unpacked_cbi_int[6]}
add wave -noupdate -color Coral {/tb_PMU_raw/dut_PMU_raw/unpacked_cbi_int[7]}
add wave -noupdate -color Gold {/tb_PMU_raw/dut_PMU_raw/unpacked_cbo_int[0]}
add wave -noupdate -color Gold {/tb_PMU_raw/dut_PMU_raw/unpacked_cbo_int[1]}
add wave -noupdate -color Gold {/tb_PMU_raw/dut_PMU_raw/unpacked_cbo_int[2]}
add wave -noupdate -color Gold {/tb_PMU_raw/dut_PMU_raw/unpacked_cbo_int[3]}
add wave -noupdate -color Gold {/tb_PMU_raw/dut_PMU_raw/unpacked_cbo_int[4]}
add wave -noupdate -color Gold {/tb_PMU_raw/dut_PMU_raw/unpacked_cbo_int[5]}
add wave -noupdate -color Gold {/tb_PMU_raw/dut_PMU_raw/unpacked_cbo_int[6]}
add wave -noupdate -color Gold {/tb_PMU_raw/dut_PMU_raw/unpacked_cbo_int[7]}
add wave -noupdate /tb_PMU_raw/dut_PMU_raw/selftest_mode
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {275106 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 225
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {1074060 ps}

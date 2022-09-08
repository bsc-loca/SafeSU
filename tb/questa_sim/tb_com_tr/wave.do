onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_com_tr/CLK_PERIOD
add wave -noupdate /tb_com_tr/CLK_HALF_PERIOD
add wave -noupdate /tb_com_tr/CLK_QUARTER_PERIOD
add wave -noupdate /tb_com_tr/TB_IN_WIDTH
add wave -noupdate /tb_com_tr/tb_clk_i
add wave -noupdate /tb_com_tr/tb_dclk_i
add wave -noupdate /tb_com_tr/tb_rstn_i
add wave -noupdate /tb_com_tr/tb_signal_i
add wave -noupdate /tb_com_tr/tb_error_o
add wave -noupdate /tb_com_tr/tb_test_name
add wave -noupdate /tb_com_tr/tb_fail
add wave -noupdate -expand -group internal /tb_com_tr/dut_com_tr/IN_WIDTH
add wave -noupdate -expand -group internal /tb_com_tr/dut_com_tr/clk_i
add wave -noupdate -expand -group internal /tb_com_tr/dut_com_tr/dclk_i
add wave -noupdate -expand -group internal /tb_com_tr/dut_com_tr/rstn_i
add wave -noupdate -expand -group internal /tb_com_tr/dut_com_tr/signal_i
add wave -noupdate -expand -group internal /tb_com_tr/dut_com_tr/error_o
add wave -noupdate -expand -group internal /tb_com_tr/dut_com_tr/reg1
add wave -noupdate -expand -group internal /tb_com_tr/dut_com_tr/reg2
add wave -noupdate /tb_com_tr/dut_com_tr/error_int
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {38000 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 343
configure wave -valuecolwidth 529
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ps} {56700 ps}

onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix ascii /tb_reg_sbf/tb_test_name
add wave -noupdate /tb_reg_sbf/dut_reg_sbf/clk_i
add wave -noupdate /tb_reg_sbf/dut_reg_sbf/rstn_i
add wave -noupdate /tb_reg_sbf/dut_reg_sbf/regi_i
add wave -noupdate /tb_reg_sbf/dut_reg_sbf/rego_i
add wave -noupdate /tb_reg_sbf/dut_reg_sbf/error_o
add wave -noupdate /tb_reg_sbf/dut_reg_sbf/parity1_int
add wave -noupdate /tb_reg_sbf/dut_reg_sbf/parity2_int
add wave -noupdate /tb_reg_sbf/dut_reg_sbf/reg_parity_int
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {2473712000 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 556
configure wave -valuecolwidth 100
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
WaveRestoreZoom {0 ps} {1049407392 ps}

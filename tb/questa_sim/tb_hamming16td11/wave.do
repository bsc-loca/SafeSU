onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix ascii /tb_hamming16t11d/tb_test_name
add wave -noupdate /tb_hamming16t11d/tb_clk_i
add wave -noupdate -color Orange -itemcolor Red /tb_hamming16t11d/upset_value
add wave -noupdate -color Orange -itemcolor Red /tb_hamming16t11d/valid_value
add wave -noupdate -color Coral -itemcolor Red /tb_hamming16t11d/dbg_andhv
add wave -noupdate -color Magenta /tb_hamming16t11d/trasient
add wave -noupdate -color {Medium Spring Green} /tb_hamming16t11d/dut_hamming16t11d_enc/data_i
add wave -noupdate -color {Cornflower Blue} -itemcolor Black /tb_hamming16t11d/dut_hamming16t11d_dec/data_o
add wave -noupdate -color {Medium Spring Green} /tb_hamming16t11d/dut_hamming16t11d_enc/hv_o
add wave -noupdate -color {Cornflower Blue} -itemcolor Black /tb_hamming16t11d/dut_hamming16t11d_dec/ded_error_o
add wave -noupdate -color {Cornflower Blue} -itemcolor Black /tb_hamming16t11d/dut_hamming16t11d_dec/hv_i
add wave -noupdate -color Coral /tb_hamming16t11d/prot_reg
add wave -noupdate /tb_hamming16t11d/tb_din_i
add wave -noupdate /tb_hamming16t11d/tb_dout_o
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {31886 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 621
configure wave -valuecolwidth 157
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
WaveRestoreZoom {0 ps} {33600 ps}

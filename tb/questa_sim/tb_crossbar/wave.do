onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix ascii /tb_crossbar/tb_test_name
add wave -noupdate /tb_crossbar/tb_clk_i
add wave -noupdate /tb_crossbar/tb_rstn_i
add wave -noupdate {/tb_crossbar/tb_vector_i[1]}
add wave -noupdate {/tb_crossbar/tb_vector_o[1]}
add wave -noupdate {/tb_crossbar/tb_cfg_i[1]}
add wave -noupdate /tb_crossbar/tb_vector_i
add wave -noupdate /tb_crossbar/tb_vector_o
add wave -noupdate {/tb_crossbar/tb_vector_i[5]}
add wave -noupdate {/tb_crossbar/tb_cfg_i[6]}
add wave -noupdate /tb_crossbar/tb_cfg_i
add wave -noupdate /tb_crossbar/tb_fail
add wave -noupdate /tb_crossbar/dut_crossbar/N_OUT
add wave -noupdate /tb_crossbar/dut_crossbar/N_IN
add wave -noupdate /tb_crossbar/dut_crossbar/N_BITS_CFG
add wave -noupdate /tb_crossbar/dut_crossbar/clk_i
add wave -noupdate /tb_crossbar/dut_crossbar/rstn_i
add wave -noupdate /tb_crossbar/dut_crossbar/vector_i
add wave -noupdate /tb_crossbar/dut_crossbar/vector_o
add wave -noupdate /tb_crossbar/dut_crossbar/cfg_i
add wave -noupdate /tb_crossbar/dut_crossbar/mux_int
add wave -noupdate {/tb_crossbar/dut_crossbar/mux[6]/x}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1043 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 334
configure wave -valuecolwidth 169
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
WaveRestoreZoom {0 ps} {12600 ps}

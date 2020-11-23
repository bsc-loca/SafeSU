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
add wave -noupdate /tb_crossbar/tb_cfg_i
add wave -noupdate /tb_crossbar/tb_fail
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {17884 ps} 0}
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
WaveRestoreZoom {7575 ps} {51540 ps}

onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -height 40 /tb_MCCU/dut_MCCU/clk_i
add wave -noupdate -height 40 /tb_MCCU/dut_MCCU/rstn_i
add wave -noupdate -height 40 /tb_MCCU/dut_MCCU/enable_i
add wave -noupdate -height 40 -radix decimal /tb_MCCU/dut_MCCU/quota_i
add wave -noupdate -height 40 -radix decimal /tb_MCCU/dut_MCCU/quota_int
add wave -noupdate -height 40 -radix decimal /tb_MCCU/dut_MCCU/quota_o
add wave -noupdate -height 40 /tb_MCCU/dut_MCCU/interruption_quota_o
add wave -noupdate -height 40 -radix unsigned -childformat {{{/tb_MCCU/dut_MCCU/events_weights_i[0]} -radix unsigned}} -expand -subitemconfig {{/tb_MCCU/dut_MCCU/events_weights_i[0]} {-height 40 -radix unsigned}} /tb_MCCU/dut_MCCU/events_weights_i
add wave -noupdate -height 40 /tb_MCCU/dut_MCCU/events_i
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {8031 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 259
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
WaveRestoreZoom {0 ps} {35026 ps}

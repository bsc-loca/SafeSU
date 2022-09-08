onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -height 40 /tb_MCCU/dut_MCCU/clk_i
add wave -noupdate -height 40 /tb_MCCU/dut_MCCU/rstn_i
add wave -noupdate -height 40 /tb_MCCU/dut_MCCU/enable_i
add wave -noupdate -height 40 -radix decimal /tb_MCCU/dut_MCCU/quota_i
add wave -noupdate -height 40 -radix decimal -childformat {{{/tb_MCCU/dut_MCCU/quota_int[0]} -radix decimal} {{/tb_MCCU/dut_MCCU/quota_int[1]} -radix decimal} {{/tb_MCCU/dut_MCCU/quota_int[2]} -radix decimal} {{/tb_MCCU/dut_MCCU/quota_int[3]} -radix decimal}} -expand -subitemconfig {{/tb_MCCU/dut_MCCU/quota_int[0]} {-radix decimal} {/tb_MCCU/dut_MCCU/quota_int[1]} {-radix decimal} {/tb_MCCU/dut_MCCU/quota_int[2]} {-radix decimal} {/tb_MCCU/dut_MCCU/quota_int[3]} {-radix decimal}} /tb_MCCU/dut_MCCU/quota_int
add wave -noupdate -height 40 -radix decimal /tb_MCCU/dut_MCCU/quota_o
add wave -noupdate -height 40 -expand /tb_MCCU/dut_MCCU/interruption_quota_o
add wave -noupdate -height 40 -radix unsigned -childformat {{{/tb_MCCU/dut_MCCU/events_weights_i[0]} -radix unsigned} {{/tb_MCCU/dut_MCCU/events_weights_i[1]} -radix unsigned} {{/tb_MCCU/dut_MCCU/events_weights_i[2]} -radix unsigned} {{/tb_MCCU/dut_MCCU/events_weights_i[3]} -radix unsigned}} -expand -subitemconfig {{/tb_MCCU/dut_MCCU/events_weights_i[0]} {-height 40 -radix unsigned} {/tb_MCCU/dut_MCCU/events_weights_i[1]} {-height 31 -radix unsigned} {/tb_MCCU/dut_MCCU/events_weights_i[2]} {-height 31 -radix unsigned} {/tb_MCCU/dut_MCCU/events_weights_i[3]} {-height 31 -radix unsigned}} /tb_MCCU/dut_MCCU/events_weights_i
add wave -noupdate -height 40 /tb_MCCU/dut_MCCU/events_i
add wave -noupdate /tb_MCCU/dut_MCCU/update_quota_i
add wave -noupdate /tb_MCCU/dut_MCCU/ccc_suma_int
add wave -noupdate /tb_MCCU/dut_MCCU/interruption_quota_d
add wave -noupdate /tb_MCCU/dut_MCCU/interruption_quota_q
add wave -noupdate -radix ascii /tb_MCCU/tb_test_name
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {14000 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 592
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
WaveRestoreZoom {509 ps} {57774 ps}

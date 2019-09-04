onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_AXI_PMU/tb_clk_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/events_i
add wave -noupdate -expand /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/slv_reg
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/MCCU_int_o
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/int_quota_o
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/int_overflow_o
add wave -noupdate -color Salmon /tb_AXI_PMU/tb_run
add wave -noupdate -color Salmon /tb_AXI_PMU/tb_rstn_i
add wave -noupdate -color Salmon /tb_AXI_PMU/tb_done
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_ACLK_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_RREADY_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_WSTRB_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_WDATA_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_AWADDR_i
add wave -noupdate -color Gold /tb_AXI_PMU/dut_AXI_PMU/S_AXI_AWVALID_i
add wave -noupdate -color Gold /tb_AXI_PMU/dut_AXI_PMU/S_AXI_WVALID_i
add wave -noupdate -color Gold /tb_AXI_PMU/dut_AXI_PMU/S_AXI_WREADY_o
add wave -noupdate -color Gold /tb_AXI_PMU/dut_AXI_PMU/S_AXI_AWREADY_o
add wave -noupdate -color Gold /tb_AXI_PMU/dut_AXI_PMU/S_AXI_BVALID_o
add wave -noupdate -color Gold /tb_AXI_PMU/dut_AXI_PMU/S_AXI_RVALID_o
add wave -noupdate -color Gold /tb_AXI_PMU/dut_AXI_PMU/S_AXI_BREADY_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_RRESP_o
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_BRESP_o
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_ARREADY_o
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_ARVALID_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_ARESETN_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_ARADDR_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/S_AXI_RDATA_o
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {24000 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 343
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
WaveRestoreZoom {529276 ps} {603723 ps}

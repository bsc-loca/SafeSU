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
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generated_quota/suma
add wave -noupdate /tb_AXI_PMU/int_quota_c0_o
add wave -noupdate /tb_AXI_PMU/int_quota_c1_o
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/ccc_suma_int
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/clk_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/CORE_EVENTS
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/D_W_0PAD
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/DATA_WIDTH
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/enable_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/events_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/events_weights_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/events_weights_int
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/interruption_quota_o
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/j
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/N_CORES
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/O_D_0PAD
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/O_W_0PAD
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/OVERFLOW_PROT
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/quota_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/quota_int
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/quota_o
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/rstn_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/update_quota_i
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/inst_MCCU/WEIGHTS_WIDTH
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/MCCU_events_weights_int
add wave -noupdate /tb_AXI_PMU/dut_AXI_PMU/inst_AXI_PMU/generate_MCCU/weights_flat_bitarray
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1766058 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 506
configure wave -valuecolwidth 241
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
WaveRestoreZoom {1741372 ps} {1829568 ps}

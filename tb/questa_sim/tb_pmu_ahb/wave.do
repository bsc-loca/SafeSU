onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_pmu_ahb/haddr_i
add wave -noupdate /tb_pmu_ahb/hrdata_o
add wave -noupdate /tb_pmu_ahb/htrans_i
add wave -noupdate /tb_pmu_ahb/hwdata_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/regs_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/regs_o
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/crossbar_cfg
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/pmu_regs_int
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/next
add wave -noupdate -radix unsigned -radixshowbase 0 /tb_pmu_ahb/dut_pmu_ahb/slv_index
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/hwrite_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/hsel_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/clk_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/rstn_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/haddr_i
add wave -noupdate /tb_pmu_ahb/htrans_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/events_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/clk_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/rstn_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/softrst_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/en_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/we_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/regs_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/regs_o
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/events_i
add wave -noupdate -expand /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/slv_reg
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/adder_out
add wave -noupdate -expand -subitemconfig {{/tb_pmu_ahb/dut_pmu_ahb/slv_reg[29]} -expand} /tb_pmu_ahb/dut_pmu_ahb/slv_reg
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/slv_reg_D
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/slv_reg_Q
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/CORE_EVENTS
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/D_W_0PAD
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/DATA_WIDTH
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/enable_i
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/events_i
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/events_weights_i
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/events_weights_int
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/FT
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/interruption_quota_d
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/interruption_quota_o
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/interruption_quota_q
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/intr_FT1_o
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/intr_FT2_o
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/N_CORES
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/O_D_0PAD
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/O_W_0PAD
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/OVERFLOW_PROT
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_i
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_o
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/rstn_i
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/update_quota_i
add wave -noupdate -itemcolor {Medium Violet Red} /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/WEIGHTS_WIDTH
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/MCCU_softrst
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_i
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_i[0]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_i[1]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_i[2]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_i[3]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_i[4]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_i[5]}
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_o
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_o[0]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_o[1]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_o[2]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_o[3]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_o[4]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/quota_o[5]}
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/rstn_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_MCCU/update_quota_i
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/slv_reg[29][2]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/slv_reg[29][3]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/slv_reg[29][4]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/slv_reg[29][5]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/slv_reg[29][6]}
add wave -noupdate {/tb_pmu_ahb/dut_pmu_ahb/slv_reg[29][7]}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {256000 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 299
configure wave -valuecolwidth 252
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
configure wave -timelineunits ns
update
WaveRestoreZoom {245174 ps} {317092 ps}

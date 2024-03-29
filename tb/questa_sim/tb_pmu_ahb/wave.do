onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/regs_i
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/regs_o
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/crossbar_cfg
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/pmu_regs_int
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/state
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
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/slv_reg
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/inst_pmu_raw/inst_counters/adder_out
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/intr_FT_o
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/HAM_P
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/HAM_D
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/HAM_M
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/N_HAM32_SLV
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/ift_slv
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/slv_reg_fti
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/slv_reg_fto
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/slv_reg_ufto
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/slv_reg_pQ
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/ham_mbits_D
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/ham_mbits_Q
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/genblk1/ham_pbits
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/slv_reg
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/slv_reg_D
add wave -noupdate /tb_pmu_ahb/dut_pmu_ahb/slv_reg_Q
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {5996 ps} 0}
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
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {119739 ps}

//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Integrate PMU and AHB interface
// Description: AHB interface implementation of the  PMU. 
//              
//              This module is responsible managing reads and writes from and
//              AHB master and interface with pmu_ahb module.
//
// Coder      : G.Cabo
// References : AMBA 3 AHB-lite  specifications 
//              ARM IHI 0033A  
// Notes      : Any write to a control registers takes 2 clock cycles to
//              take effect since it propagates from the wrapper to the
//              internal regs of the PMU

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
	module top #
	(
        parameter integer haddr = 0,                                                  
        parameter integer hmask  = 0,                                           
		// Width of registers data bus
        parameter integer REG_WIDTH = 32,
        // Number of counters
        parameter integer PMU_COUNTERS = 24,
        // Number of SoC events
        parameter integer N_SOC_EV = 32,
        // Total amount of registers (use ahb_pmu_mem_map.ods) 
        parameter integer N_REGS = 47, 
        // Fault tolerance mechanisms (FT==0 -> FT disabled)
        parameter integer FT  = 0,                                           
	// -- Local parameters
		//haddr width
        localparam integer HADDR_WIDTH = 32,
		//hdata width
        localparam integer HDATA_WIDTH = 32,
		// Cores connected to MCCU
        localparam MCCU_N_CORES = 4,
		// Number of configuration registers
        localparam PMU_CFG = 1
	)
	(
         input wire rstn_i,
         input wire clk_i,
    //  -- AHB bus slave interface                                              
        // slave select
        input wire         hsel_i,                               
        // previous transfer done 
        input wire         hreadyi_i,
        // address bus 
        input wire [HADDR_WIDTH-1:0]  haddr_i,
        // read/write 
        input wire         hwrite_i,
        // transfer type
        input wire [1:0]   htrans_i,
        // transfer size
        input wire [2:0]   hsize_i,
        // burst type
        input wire [2:0]   hburst_i,
        // write data bus
        input wire [HDATA_WIDTH-1:0]  hwdata_i,
        // prtection control
        input wire [3:0]   hprot_i,
        // locked access 
        input wire         hmastlock_i,
    // -- PMU specific signales
        input wire [N_SOC_EV-1:0] events_i,

        //outputs of FT unit
        output logic fthreadyo_o,
        output logic [1:0] fthresp_o,
        output logic [HDATA_WIDTH-1:0] fthrdata_o,
        output logic ftintr_overflow_o,
        output logic ftintr_quota_o,
        output logic [MCCU_N_CORES-1:0] ftintr_MCCU_o,
        output logic ftintr_RDC_o,
        output logic ftintr_FT1_o,
        output logic ftintr_FT2_o,
        //outputs of non-FT unit
        output logic hreadyo_o,
        output logic [1:0] hresp_o,
        output logic [HDATA_WIDTH-1:0] hrdata_o,
        output logic intr_overflow_o,
        output logic intr_quota_o,
        output logic [MCCU_N_CORES-1:0] intr_MCCU_o,
        output logic intr_RDC_o,
        output logic intr_FT1_o,
        output logic intr_FT2_o
    );

	pmu_ahb #
	(
        .haddr(32'h80100000),                                                  
        .hmask(32'hfff),                                           
        .REG_WIDTH(32),
        .FT(1),
        .N_REGS(47) 
	)
    dut_ft_pmu_ahb 
	(
        .rstn_i(rstn_i),
        .clk_i(clk_i),
        .hsel_i(hsel_i),                               
        .hreadyi_i(1'b1),
        .haddr_i(haddr_i),
        .hwrite_i(hwrite_i),
        .htrans_i(htrans_i),
        .hsize_i(3'b0),
        .hburst_i(3'b0),
        .hwdata_i(hwdata_i),
        .hprot_i(4'b0),
        .hmastlock_i(1'b0),
        .hreadyo_o(fthreadyo_o),
        .hresp_o(fthresp_o),
        .hrdata_o(fthrdata_o),
        .events_i(events_i),
        .intr_overflow_o(ftintr_overflow_o),
        .intr_quota_o(ftintr_quota_o),
        .intr_MCCU_o(ftintr_MCCU_o),
        .intr_RDC_o(ftintr_RDC_o),
        .intr_FT1_o(ftintr_FT1_o),
        .intr_FT2_o(ftintr_FT2_o)

    );
	
    pmu_ahb #
	(
        .haddr(32'h80100000),                                                  
        .hmask(32'hfff),                                           
        .REG_WIDTH(32),
        .FT(0),
        .N_REGS(47) 
	)
    dut_pmu_ahb 
	(
        .rstn_i(rstn_i),
        .clk_i(clk_i),
        .hsel_i(hsel_i),                               
        .hreadyi_i(1'b1),
        .haddr_i(haddr_i),
        .hwrite_i(hwrite_i),
        .htrans_i(htrans_i),
        .hsize_i(3'b0),
        .hburst_i(3'b0),
        .hwdata_i(hwdata_i),
        .hprot_i(4'b0),
        .hmastlock_i(1'b0),
        .hreadyo_o(hreadyo_o),
        .hresp_o(hresp_o),
        .hrdata_o(hrdata_o),
        .events_i(events_i),
        .intr_overflow_o(intr_overflow_o),
        .intr_quota_o(intr_quota_o),
        .intr_MCCU_o(intr_MCCU_o),
        .intr_RDC_o(intr_RDC_o),
        .intr_FT1_o(intr_FT1_o),
        .intr_FT2_o(intr_FT2_o)
    );
// Assert equivalence between FT and non-FT  modules
`ifdef	EQ_CHECK
    // Initialize formal
    reg f_past_valid ;
    initial f_past_valid = 1'b0;
    always@( posedge clk_i )
        f_past_valid <= 1'b1;
    //Clocking
    default clocking @(posedge clk_i); endclocking;
    //Assumptions
    assume property ((!f_past_valid) |-> (rstn_i==0));
    //Assertions
    // Outputs of both modules shall be the same at all times
    assert property ((f_past_valid) |=>  (hreadyo_o == fthreadyo_o));
    assert property ((f_past_valid) |=> (hresp_o == fthresp_o));
    assert property ((f_past_valid) |=> (hrdata_o == fthrdata_o));
    assert property ((f_past_valid) |=> (intr_overflow_o == ftintr_overflow_o));
    //Quota mechanism is deprecated
    //assert property ((f_past_valid) |=> (intr_quota_o == ftintr_quota_o));
    assert property ((f_past_valid) |=> (intr_MCCU_o == ftintr_MCCU_o));
    assert property ((f_past_valid) |=> (intr_RDC_o == ftintr_RDC_o));
    assert property ((f_past_valid) |=> (intr_FT1_o == ftintr_FT1_o));
    assert property ((f_past_valid) |=> (intr_FT2_o == ftintr_FT2_o));

`endif
endmodule
`default_nettype wire //allow compatibility with legacy code and xilinx ip


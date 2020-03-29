//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Integrate PMU features under one module
// Description: Interface agnostic implementation of the  PMU. Values of the
//              PMU are registered in this module.
//              
//              This module is responsible of configure the memory map, handle
//              write / read syncronization with a higher level module that
//              integrates standar bus interfaces such as AXI, AHB or wishbone.
//
//              Parametrization of the features is configured here by
//              replicating instances of features and adjusting basic
//              parameters such as counters width.
//
// Coder      : G.Cabo
// References : Implementation of Maximum-Contention Control Unit (MCCU): 
//              ResourceAccess Count and Contention Time Enforcement. 
//              https://upcommons.upc.edu/handle/2117/133656

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
	module PMU_raw #
	(
		// Width of registers data bus
		parameter integer REG_WIDTH	= 32,
		// Width of registers IDs
		parameter integer REG_ID_WIDTH	= 5,
		// Amount of counters
		parameter integer N_COUNTERS	= 9,
		// Configuration registers
		parameter integer N_CONF_REGS	= 1,
		// Overflow
		parameter integer OVERFLOW	= 0, //Yes/No
		// Quota
		parameter integer QUOTA	= 0, //Yes/No
		// MCCU - Maximum-contention Control Unit mode
		parameter integer MCCU	= 0, //Yes/No
		// MCCU - N_CORES
		parameter integer N_CORES	= 1, 
        //
        parameter integer TOTAL_NREGS = N_COUNTERS + N_CONF_REGS
	)
	(
/*        //interruptions risen when one event exceeds it expected max duration
        output wire int_rdc_o,
        //interruptions risen when cores exceeds the quota of MCCU
        output wire MCCU_int_o [N_CORES-1:0],
        //interruption rises when one of the counters overflows
        output reg int_overflow_o,
        //interruption rises when the total of cuota consumed is exceeded
        output wire int_quota_o,
        //external signals from Soc events
        input wire [N_COUNTERS-1:0] events_i, // bus of signals for counters 
		// Global Clock Signal
		input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
        // Input/output wire from registers of the wrapper to PMU_raw internal
        // registers
        input wire [REG_WIDTH-1:0] regs_i [0:TOTAL_NREGS-1],
        output wire [REG_WIDTH-1:0] regs_o [0:TOTAL_NREGS-1],
        // Wrapper writte enable
        input wire wrapper_we_i,
        // Wrapper writte addres
        input wire [REG_ID_WIDTH-1:0] wrapper_wa_i
*/        
	);
//----------------------------------------------
//------------- Counters instance
//----------------------------------------------
    PMU_counters # (
		.REG_WIDTH	(32),
		.N_COUNTERS	(9)
	)
    inst_counters (
		.clk_i      (),
		.rstn_i     (),
		.softrst_i  (),
		.en_i       (),
		.we_i       (),
        .regs_i     (),
        .regs_o     (),
        .events_i   () 
	);

//----------------------------------------------
//------------- Overflow interuption instance
//----------------------------------------------
    PMU_overflow # (
		.REG_WIDTH	(32),
		.N_COUNTERS	(9)
	)
    inst_overflow (
		.clk_i              (),
		.rstn_i             (),
		.softrst_i          (),
		.en_i               (),
        .counter_regs_i     (),
        .over_intr_mask_i   (), 
        .intr_overflow_o    (), 
        .over_intr_vect_o   ()
	);

//----------------------------------------------
//------------- Quota interruption instance
//----------------------------------------------
    PMU_quota # (
        .REG_WIDTH	(32),
        .N_COUNTERS	(9)
    )
    inst_quota(
        .clk_i          (),
        .rstn_i         (),
        .counter_value_i(),
        .softrst_i      (),
        .quota_limit_i  (),
        .quota_mask_i   (), 
        .intr_quota_o   () 
    );

//----------------------------------------------
//------------- MCCU instance
//----------------------------------------------
    MCCU # (
        // Width of data registers
        .DATA_WIDTH     (MCCU_DATA_WIDTH),
        // Width of weights registers
        .WEIGHTS_WIDTH  (MCCU_WEIGHTS_WIDTH),
        //Cores. Change this may break Verilator TB
        .N_CORES        (MCCU_N_CORES),
        //Signals per core. Change this may break Verilator TB
        .CORE_EVENTS    (MCCU_CORE_EVENTS)
    )
    inst_MCCU(
        .clk_i                  (clk_i),
        .rstn_i                 (rstn_i || MCCU_rstn_int),
        .enable_i               (MCCU_enable_int),// Software map
        .events_i               (events_int),//how to parametrize this? new parameter on top or up to the programer that does the integration?
        .quota_i                (MCCU_quota_int),//One register per core
        .update_quota_i         (MCCU_update_quota_int),//Software map
        .quota_o                (MCCU_quota_o),//write back to a read register
        .events_weights_i       (MCCU_events_weights_int),//core_events times WEIGHTS_WIDTH registers
        .interruption_quota_o   (MCCU_int_o)//N_CORES output signals Add this to top or single toplevel interrupt and an interrupt vector that identifies the source?
                                   // Individual interrupts allow each core to
                                   // handle their own interrupts , therefore
                                   //it seems to be te right solution.
    );

//----------------------------------------------
//------------- Request Duration Counter (RDC) 
//----------------------------------------------
    RDC #(
        // Width of data registers
        .DATA_WIDTH     (MCCU_DATA_WIDTH),
        // Width of weights registers
        .WEIGHTS_WIDTH  (MCCU_WEIGHTS_WIDTH),
        //Cores. 
        .N_CORES        (MCCU_N_CORES),
        //Signals per core. 
        .CORE_EVENTS    (MCCU_CORE_EVENTS)
    ) inst_RDC(
        .clk_i                  (clk_i),
        .rstn_i                 (rstn_i || MCCU_rstn_int ),
        .enable_i               (MCCU_enable_int),// Software map
        .events_i               (events_int),//how to parametrize this? new parameter on top or up to the programer that does the integration?
        .events_weights_i       (MCCU_events_weights_int),//core_events times WEIGHTS_WIDTH registers
        .interruption_rdc_o(intr_rdc_o),// interruption signaling a signal has exceed the expected maximum request time
        .interruption_vector_rdc_o(intrv_rdc_int) // vector with offending
            //signals. One hot encoding.
            //Cleared when MCCU is disabled.
    );

////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip


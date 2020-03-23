//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Submodule of the PMU to handle counters 
// Description: This module is contains the adders and registers for the PMU
//              the registers are exposed through the interface to the modules
//              other modules of the PMU and passed through to the PMU wrapper
//              through the module PMU_raw
//
// Coder      : G.Cabo
// References : 

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
module PMU_counters #
	(
		// Width of registers data bus
		parameter integer REG_WIDTH	= 32,
		// Amount of counters
		parameter integer N_COUNTERS	= 9
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
		// Soft Reset Signal from configuration registeres. This Signal is 
        // Active HIGH
		input wire  softrst_i,
		// Enable Signal from configuration registeres. This Signal is 
        // Active HIGH
		input wire  en_i,
		// Write enable signal. When this signal is high any value in regs_i
        // is feed in to the internal registers. The Wrapper has to  ensure
        // that the propper values are feeded in.
        // rst_i and softrst_i, have priority over we_i.
        //TODO: Consider if is worth adding acces to individual registers
		input wire  we_i,

        // Input/output wire from registers of the wrapper to PMU_raw internal
        // registers
        input wire [REG_WIDTH-1:0] regs_i [0:N_COUNTERS-1],
        output wire [REG_WIDTH-1:0] regs_o [0:N_COUNTERS-1],
        //external signals from Soc events
        input wire [N_COUNTERS-1:0] events_i 
	);
    reg [REG_WIDTH-1:0] slv_reg [0:N_COUNTERS-1] /*verilator public*/;
//-------------Adders with reset
    //Inside the generate loop it creates as many counters as the parameter
    //N_COUNTERS. For each of them one slv_reg is assigned. When a soft reset
    //(softrst_i high) or hard reset (rstn_i) slv_registers are set
    //to 0. If non of this cases happen if the PMU is enabled (en_i high) and
    //the event of the given counter (events_i[k]) is high the counter
    // increases by one.
    always @(posedge clk_i, negedge rstn_i) begin
        integer i;
        if(rstn_i == 1'b0 ) begin
            for (i=0; i<N_COUNTERS; i=i+1) begin
                slv_reg[i] <={REG_WIDTH{1'b0}};
            end
        end else begin
            for (i=0; i<N_COUNTERS; i=i+1) begin
                if(softrst_i) slv_reg[i] <={REG_WIDTH{1'b0}};
                else if (we_i) slv_reg <= regs_i;
                else if(events_i[i] & en_i) slv_reg[i] <= slv_reg[i]+1;
            end
        end
    end
//Map input and output registers
    assign regs_o = slv_reg;
//TODO: fill formal propperties
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip

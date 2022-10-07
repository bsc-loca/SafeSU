//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Single event transient error detector for comb. logic. 
// Description: This module takes a signal coming from a combinational block 
//              and registers the signal at two different points of the clock cycle.
//              To achive that two clocks are needed, one is the regular system clock
//              , the other has to be delayed by  a given amount based on the type
//              of faults and the clock period of the implementation. 
//
// Coder      : G.Cabo
// References : Fault-Tolerance Techniques for SRAM-Based FPGAs - ISBN 978-0-387-31069-5 

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
module com_tr #
	(
		// Width of sampled signal
		parameter integer IN_WIDTH	= 1
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Delayed Clock Signal. Delay can't be larger than clock cycle. 
		input wire  dclk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
		// Signal to monitor
        input wire [IN_WIDTH-1:0] signal_i,
		// Enable for error detection
        output reg  error_o
	);
    logic [IN_WIDTH-1:0] reg1;
    logic [IN_WIDTH-1:0] reg2;
    logic error_int;

    //Register sampling at global clock
    always_ff @(posedge clk_i) begin
        if(rstn_i == 1'b0 ) begin
            reg1<='{default:0};
        end else begin
            reg1<=signal_i;
        end
    end
    
    //Register sampling at delayed clock
    always_ff @(posedge dclk_i) begin
        if(rstn_i == 1'b0 ) begin
            reg2<='{default:0};
        end else begin
            reg2<=signal_i;
        end
    end
   
    //XOR the values of registers to detect errors. OR all XORed bits to rise the
    //error signal. 
    assign error_int = |(reg1 ^ reg2); 
    //Register the outcome at the next positive edge to avoid false errors
    //  due to clock and dcloc sync
    always_ff @(posedge clk_i) begin
        error_o <= error_int;
    end
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip

//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Single bit-flip error detector circuit.
// Description: This module takes a signals coming from the input of a register,
//              computes an even parity bit at the input and registers its value. The output
//              of the monitored register is used afterwards to compute again the parity bit.
//              If the parity bit at the output is different to the previous parity bit and
//              error is signaled.
//
//              Number of ones for data + parity bit shall be even.
//
//              Error signal is only active while the bit-flip is present in the circuit aka
//              the error signal is NOT holded until it is handled.
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
module reg_sbf #
	(
		// Width of sampled signal
		parameter integer IN_WIDTH	= 32
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
		// Signal at register input
        input wire [IN_WIDTH-1:0] regi_i,
		// Signal at register output
        input wire [IN_WIDTH-1:0] rego_i,
		// Enable for error detection
        output reg  error_o
	);
    logic parity1_int; //parity bit at input
    logic parity2_int; //parity bit at output
    logic reg_parity_int; // parity bit from input register

    //Get parity from input of register and register value
    assign parity1_int = ^regi_i;
    always_ff @(posedge clk_i) begin
        if(!rstn_i) begin
            reg_parity_int <= 1'b0;
        end else begin
            reg_parity_int <= parity1_int;
        end
    end
    
    //Get parity from output of register
    assign parity2_int = ^rego_i;

    //Compare parity bits and signal error if discrepancy
    assign error_o = (parity2_int == reg_parity_int)? 1'b0:1'b1;
    
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip

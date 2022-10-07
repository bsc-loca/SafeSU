//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Instance of several protection elements in paralel
// Description: Instances for area/resources and frequency comparison of
//              hamming16t11d, , reg_sbf, and com_tr fault tolerance mechanisms.
//              All resources are configured to protect signals/registers of 
//              8, 11, 32 and 64 bits. 
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
module instances #
	(
    `ifdef D4
		// Width of sampled signal
		parameter integer IN_WIDTH	= 4
    `elsif D8
		// Width of sampled signal
		parameter integer IN_WIDTH	= 8
    `elsif D11
		// Width of sampled signal
		parameter integer IN_WIDTH	= 11
    `elsif D16
		// Width of sampled signal
		parameter integer IN_WIDTH	= 16
    `elsif D32
		// Width of sampled signal
		parameter integer IN_WIDTH	= 32
    `elsif D64
		// Width of sampled signal
		parameter integer IN_WIDTH	= 64
    `else
		// Width of sampled signal
		parameter integer IN_WIDTH	= 32
    `endif
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Delayed Clock Signal
		input wire  dclk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
		// data input
        input wire [IN_WIDTH-1:0] din_i,
        //Output signals from IPs
        output logic com_error,
        output logic [IN_WIDTH-1:0] trip_dout,
        output logic trip_error1,
        output logic trip_error2,
        output logic sbf_error,
        output logic [11-1:0] ham_dout,
        output logic ham_error
        
	);
// Time delayed error detection for COMB - Multiple bits error detection
    com_tr #(
		.IN_WIDTH(IN_WIDTH)
	)dut_com_tr (
		.clk_i(clk_i),
		.dclk_i(dclk_i),
		.rstn_i(rstn_i),
		.signal_i(din_i),
		.error_o(com_error)
	);
// Triplicated register - Multiple bits error detection
    triple_reg#(.IN_WIDTH(IN_WIDTH)
    )dut_trip(
    .clk_i(clk_i),
    .rstn_i(rstn_i),
    .din_i(din_i),
    .dout_o(trip_dout),
    .error1_o(trip_error1),
    .error2_o(trip_error2)
    );
// Parity bit - Single error detection
    sbf_reg#(.IN_WIDTH(IN_WIDTH)
    )dut_sbf(
    .clk_i(clk_i),
    .rstn_i(rstn_i),
    .din_i(din_i),
    .error_o(sbf_error)
	);
// Hamming - SECDEC 
    //TODO: Hamming is not parametrtic
    ham_reg#(.IN_WIDTH(11)
    )dut_ham(
    .clk_i(clk_i),
    .rstn_i(rstn_i),
    .din_i(din_i[10:0]),
    .dout_o(ham_dout),
    .error_o(ham_error)
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



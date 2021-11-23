//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Instance of register with hamming SECDEC protection
// Description: 
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
module ham_reg #
	(
		// Width of sampled signal
		parameter integer IN_WIDTH	= 11
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
		// data input
        input wire [IN_WIDTH-1:0] din_i,
		// data out
        output wire [IN_WIDTH-1:0] dout_o,
        // Two errors detected NON corrected
        output wire error_o
	);
    logic [16-1:0] ham_preg;
    logic [16-1:0] ham_preg_d;
    logic [16-1:0] ham_preg_q;
    logic [11-1:0] ham_dout;
    logic ham_error;
    
    //encoder
    hamming16t11d_enc#(
    )dut_hamming16t11d_enc (
        .data_i(din_i[11-1:0]),
        .hv_o(ham_preg_d)
    );
    // Instance of protected register and output wires
    always_ff @(posedge clk_i) begin
    if(!rstn_i) begin
        ham_preg <= '{default:'0};
    end else begin
        ham_preg <= ham_preg_d ;
    end
    end
    assign ham_preg_q = ham_preg;
    //decoder
    hamming16t11d_dec#(
    )dut_hamming16t11d_dec (
        .data_o(ham_dout),
        .hv_i(ham_preg_q),
        .ded_error_o(ham_error)
    );

    assign dout_o = ham_dout;
    assign error_o = ham_error;
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip

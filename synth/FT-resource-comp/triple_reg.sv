//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Instance of register with triplication and voting SECDEC
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
module triple_reg #
	(
		// Width of sampled signal
		parameter integer IN_WIDTH	= 4
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
		// data input
        input wire [IN_WIDTH-1:0] din_i,
		// data output
        output wire [IN_WIDTH-1:0] dout_o,
        // Single error detected and corrected
        output wire error1_o,
        // Two errors detected NON corrected
        output wire error2_o
        
	);
    logic [IN_WIDTH-1:0] trip0_preg;
    logic [IN_WIDTH-1:0] trip1_preg;
    logic [IN_WIDTH-1:0] trip2_preg;
    logic [IN_WIDTH-1:0] trip_preg_d;
    logic [IN_WIDTH-1:0] trip0_preg_q;
    logic [IN_WIDTH-1:0] trip1_preg_q;
    logic [IN_WIDTH-1:0] trip2_preg_q;
    logic trip_error1;
    logic trip_error2;
    logic [IN_WIDTH-1:0] trip_dout;
    
    assign trip_preg_d = din_i;
    assign trip0_preg_q = trip0_preg; 
    assign trip1_preg_q = trip1_preg; 
    assign trip2_preg_q = trip2_preg; 
    
    always_ff @(posedge clk_i) begin
        if(!rstn_i) begin
            trip0_preg <= '{default:'0};
            trip1_preg <= '{default:'0};
            trip2_preg <= '{default:'0};
        end else begin
            trip0_preg <= trip_preg_d;
            trip1_preg <= trip_preg_d;
            trip1_preg <= trip_preg_d;
        end
    end
    
    way3_voter #(
		.IN_WIDTH(IN_WIDTH)
	)dut_way3(
        .in0(trip0_preg_q),
        .in1(trip1_preg_q),
        .in2(trip2_preg_q),
        .out(trip_dout),
        .error1_o(trip_error1),
        .error2_o(trip_error2)
	);

assign dout_o = trip_dout;
assign error1_o = trip_error1;
assign error2_o = trip_error2;
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip

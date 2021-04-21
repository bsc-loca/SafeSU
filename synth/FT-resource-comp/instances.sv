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
        input wire [IN_WIDTH-1:0] din_i
        
	);
// Time delayed error detection for COMB - Multiple bits error detection
// Triplicated register - Multiple bits error detection
generate begin:triple
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
end
endgenerate

// Parity bit - Single error detection
    // Protected register and auxiliar logic
generate begin:sbf
    logic [IN_WIDTH-1:0] sbf_preg;
    logic [IN_WIDTH-1:0] sbf_preg_d;
    logic [IN_WIDTH-1:0] sbf_preg_q;
    logic sbf_error;
    assign sbf_preg_d = din_i;

    always_ff @(posedge clk_i) begin
        if(!rstn_i) begin
            sbf_preg <= '{default:'0};
        end else begin
            sbf_preg <= sbf_preg_d;
        end
    end
    assign sbf_preg_q = sbf_preg; 
    
    //***Module***
    reg_sbf #(
        .IN_WIDTH(IN_WIDTH)
    )dut_reg_sbf (
        .clk_i(clk_i),
        .rstn_i(rstn_i),
        .regi_i(sbf_preg_d),
        .rego_i(sbf_preg_q),
        .error_o(sbf_error)
    );
end
endgenerate
// Hamming - SECDEC 


////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip



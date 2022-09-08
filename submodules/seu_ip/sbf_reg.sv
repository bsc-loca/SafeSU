//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Instance of register with parity bit detection
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
module sbf_reg #
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
        // error detected
        output wire error_o
        
	);
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
    
    reg_sbf #(
        .IN_WIDTH(IN_WIDTH)
    )dut_reg_sbf (
        .clk_i(clk_i),
        .rstn_i(rstn_i),
        .regi_i(sbf_preg_d),
        .rego_i(sbf_preg_q),
        .error_o(error_o)
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

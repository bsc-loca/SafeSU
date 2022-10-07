//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Three way voter for reduncancy mechanisms
// Description: This module compares tree signals and outputs the most common value.
//              Way3u2a_voter stands for 3 inputs voter for 2D unpacked arrays
//              Takes as input an unpacked array of depth U and width W.
//              If one signal is different rises error1_o.
//              If Non of the signals is the same it rises error2_o    
//
//              Error signal is only active while the condition it describes is active.
//              
//              The circuit is combinational, is up to the designer to add input or 
//              output registers.
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
module way3u2a_voter #
	(
		// Width of sampled signal
		parameter integer W	= 32,
		// Depth of unpacked entries
		parameter integer D	= 32,
        // Number of unpacked entries
		parameter integer U	= 4
	)
	(
		// Input 0
        input wire logic [W-1:0] in0 [0:U-1][0:D-1],
		// Input 1
        input wire logic [W-1:0] in1 [0:U-1][0:D-1],
		// Input 2
        input wire logic [W-1:0] in2 [0:U-1][0:D-1],
		// Voted output
        output logic [W-1:0] out [0:U-1][0:D-1],
		// One discrepance - recovered
        output logic  error1_o,
		// Two discrepancies - unrecoverable
        output logic  error2_o
	);

    always_comb begin
        if (in0==in1) begin
            out = in0;
            if (in0!=in2) begin
                error1_o = 1'b1;
                error2_o = 1'b0;
            end else begin
                error1_o = 1'b0;
                error2_o = 1'b0;
            end
        end else begin
            error1_o = 1'b1;//Reach else implies in0!=in1
            if (in0==in2) begin
                out = in0;
                error2_o = 1'b0;
            end else begin
                if (in1==in2) begin
                    out = in1;
                    error2_o = 1'b0;
                end else begin
                    // Non of the signals match
                    // Select one input, but it may be incorrect
                    out = in0;
                    error2_o = 1'b1;
                end
            end
        end

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




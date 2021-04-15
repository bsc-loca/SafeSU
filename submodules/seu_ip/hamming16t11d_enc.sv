//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Single error corection, double error detection
// Description: This module takes 11 bits of incomming data and computes the checkbits
//              for Hamming codes.
//
// Coder      : G.Cabo
// References : Ben Eater "What is error correction? Hamming codes in hardware" YT 

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
module hamming16t11d_enc #
	(
		// Width of sampled signal
		localparam integer IN_WIDTH	= 11,
		// Number of hamming bits
		localparam integer N_CHECKB	= $clog2(IN_WIDTH) //4
	)
	(
		// Global Clock Signal
		//input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		//input wire  rstn_i,
		// Enable Signal.
		//input wire  en_i,
		// Signal at register input
        input wire [IN_WIDTH-1:0] data_i,
		// Hamming vector
        output wire [IN_WIDTH+N_CHECKB:0] hv_o
	);
    logic [N_CHECKB-1:0] hcheck_int; // hamming parity bits
    logic ocheck_int; // Overall parity bit

    //Rearrange ingputs
        //Data
    assign hv_o[3]=data_i[0];
    assign hv_o[5]=data_i[1];
    assign hv_o[6]=data_i[2];
    assign hv_o[7]=data_i[3];
    assign hv_o[9]=data_i[4];
    assign hv_o[10]=data_i[5];
    assign hv_o[11]=data_i[6];
    assign hv_o[12]=data_i[7];
    assign hv_o[13]=data_i[8];
    assign hv_o[14]=data_i[9];
    assign hv_o[15]=data_i[10];
        //Checkbits
    assign hv_o[0]=ocheck_int;
    assign hv_o[1]=hcheck_int[0];
    assign hv_o[2]=hcheck_int[1];
    assign hv_o[4]=hcheck_int[2];
    assign hv_o[8]=hcheck_int[3];
    //compute checkbits
    assign hcheck_int[0] = ^{hv_o[3],hv_o[5],hv_o[7] ,hv_o[9],hv_o[11],hv_o[13],hv_o[15]};
    assign hcheck_int[1] = ^{hv_o[3],hv_o[6],hv_o[7] ,hv_o[10],hv_o[11],hv_o[14],hv_o[15]};
    assign hcheck_int[2] = ^{hv_o[5],hv_o[6],hv_o[7] ,hv_o[12],hv_o[13],hv_o[14],hv_o[15]};
    assign hcheck_int[3] = ^{hv_o[9],hv_o[10],hv_o[11] ,hv_o[12],hv_o[13],hv_o[14],hv_o[15]};
    assign ocheck_int = ^hv_o[15:1];
/*
^data_i
^data_i[IN_WIDTH/2:0]
*/
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
    assert (IN_WIDTH==11);
    assert (N_CHECKB==4);
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip


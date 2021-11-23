//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Single error corection, double error detection
// Description: This module takes 16 bit hamming encoded package and 
//              outputs the corrected data
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
module hamming16t11d_dec #
	(
    //Parameter that does nothing but prevents tcmalloc bug VIVADO
    parameter VIVADO=0,
    // Width of sampled signal
    localparam integer IN_WIDTH	= 11,
    // Number of hamming bits
    localparam integer N_CHECKB	= $clog2(IN_WIDTH) //4
	)
	(
		// Corrected data
        output wire [IN_WIDTH-1:0] data_o,
		// Hamming vector
        input wire [IN_WIDTH+N_CHECKB:0] hv_i,
		// Double error detection signal
        output wire ded_error_o
	);
    //Locate errors
    logic [N_CHECKB-1:0] region_int;//Each parity  "region" and overall.
    assign region_int[0] = ^{hv_i[1],hv_i[3],hv_i[5],hv_i[7] ,hv_i[9],hv_i[11],hv_i[13],hv_i[15]};
    assign region_int[1] = ^{hv_i[2],hv_i[3],hv_i[6],hv_i[7] ,hv_i[10],hv_i[11],hv_i[14],hv_i[15]};
    assign region_int[2] = ^{hv_i[4],hv_i[5],hv_i[6],hv_i[7] ,hv_i[12],hv_i[13],hv_i[14],hv_i[15]};
    assign region_int[3] = ^{hv_i[8],hv_i[9],hv_i[10],hv_i[11] ,hv_i[12],hv_i[13],hv_i[14],hv_i[15]};
    assign ded_error_o = ~(^hv_i) & (region_int!=0);
    //no errors -> data correct 
    //One or Two region parity bit -> recoverable
    //Overall parity 1 ->  two errors non-recoverable

    //Flip data that needs correction
    assign data_o[0]= (3==region_int)? ~hv_i[3] : hv_i[3];
    assign data_o[1]= (5==region_int)? ~hv_i[5] : hv_i[5];
    assign data_o[2]= (6==region_int)? ~hv_i[6] : hv_i[6];
    assign data_o[3]= (7==region_int)? ~hv_i[7] : hv_i[7];
    assign data_o[4]= (9==region_int)? ~hv_i[9] : hv_i[9];
    assign data_o[5]= (10==region_int)? ~hv_i[10] : hv_i[10];
    assign data_o[6]= (11==region_int)? ~hv_i[11] : hv_i[11];
    assign data_o[7]= (12==region_int)? ~hv_i[12] : hv_i[12];
    assign data_o[8]= (13==region_int)? ~hv_i[13] : hv_i[13];
    assign data_o[9]= (14==region_int)? ~hv_i[14] : hv_i[14];
    assign data_o[10]= (15==region_int)? ~hv_i[15] : hv_i[15];
    
    /*
    genvar i;
    generate
    for(i=0;i<IN_WIDTH-1;i++) begin
        assign data_o[i]= (i==region_int)? ^hv_i[i] : hv_i[i];
    end
    endgenerate*/
/*
^data_i
^data_int[IN_WIDTH/2:0]
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


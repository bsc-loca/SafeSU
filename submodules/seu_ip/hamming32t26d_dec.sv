//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Single error corection, double error detection
// Description: This module takes 32 bit hamming encoded package and 
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
module hamming32t26d_dec #
	(
		// Width of sampled signal
		localparam integer IN_WIDTH	= 26,
		// Number of hamming bits, overall parity bit not included
		localparam integer N_CHECKB	= $clog2(IN_WIDTH) //5
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
    
    assign region_int[0] = ^{hv_i[1],hv_i[3],hv_i[5],hv_i[7],
                            hv_i[9],hv_i[11],hv_i[13],hv_i[15],
                            hv_i[17],hv_i[19],hv_i[21],hv_i[23],
                            hv_i[25],hv_i[27],hv_i[29],hv_i[31]};

    assign region_int[1] = ^{hv_i[2],hv_i[3],hv_i[6],hv_i[7],
                            hv_i[10],hv_i[11],hv_i[14],hv_i[15],
                            hv_i[18],hv_i[19], hv_i[22],hv_i[23],
                            hv_i[26],hv_i[27], hv_i[30],hv_i[31] };
    
    assign region_int[2] = ^{hv_i[4],hv_i[5],hv_i[6],hv_i[7],
                            hv_i[12],hv_i[13],hv_i[14],hv_i[15],
                            hv_i[20],hv_i[21],hv_i[22],hv_i[23],
                            hv_i[28],hv_i[29],hv_i[30],hv_i[31]};
                            
    assign region_int[3] = ^{hv_i[8],hv_i[9],hv_i[10],hv_i[11],hv_i[12],hv_i[13],hv_i[14],hv_i[15],
                             hv_i[24],hv_i[25],hv_i[26],hv_i[27],hv_i[28],hv_i[29],hv_i[30],hv_i[31]};

    assign region_int[4] = ^{hv_i[16],hv_i[17],hv_i[18],hv_i[19],hv_i[20],hv_i[21],hv_i[22],hv_i[23],
                             hv_i[24],hv_i[25],hv_i[26],hv_i[27],hv_i[28],hv_i[29],hv_i[30],hv_i[31]};
    
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
    assign data_o[11]= (17==region_int)? ~hv_i[17] : hv_i[17];
    assign data_o[12]= (18==region_int)? ~hv_i[18] : hv_i[18];
    assign data_o[13]= (19==region_int)? ~hv_i[19] : hv_i[19];
    assign data_o[14]= (20==region_int)? ~hv_i[20] : hv_i[20];
    assign data_o[15]= (21==region_int)? ~hv_i[21] : hv_i[21];
    assign data_o[16]= (22==region_int)? ~hv_i[22] : hv_i[22];
    assign data_o[17]= (23==region_int)? ~hv_i[23] : hv_i[23];
    assign data_o[18]= (24==region_int)? ~hv_i[24] : hv_i[24];
    assign data_o[19]= (25==region_int)? ~hv_i[25] : hv_i[25];
    assign data_o[20]= (26==region_int)? ~hv_i[26] : hv_i[26];
    assign data_o[21]= (27==region_int)? ~hv_i[27] : hv_i[27];
    assign data_o[22]= (28==region_int)? ~hv_i[28] : hv_i[28];
    assign data_o[23]= (29==region_int)? ~hv_i[29] : hv_i[29];
    assign data_o[24]= (30==region_int)? ~hv_i[30] : hv_i[30];
    assign data_o[25]= (31==region_int)? ~hv_i[31] : hv_i[31];
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
//    assert (IN_WIDTH==26);
//    assert (N_CHECKB==5);
`endif
endmodule
`default_nettype wire //allow compatibility with legacy code and xilinx ip

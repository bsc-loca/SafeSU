//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : Single error corection, double error detection
// Description: This module takes 26 bits of incomming data and computes the checkbits
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
module hamming32t26d_enc #
	(
    //Parameter that does nothing but prevents tcmalloc bug VIVADO
    parameter VIVADO=0,
    // Width of sampled signal
    localparam integer IN_WIDTH	= 26,
    // Number of hamming bits
    localparam integer N_CHECKB	= $clog2(IN_WIDTH) //4
	)
	(
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
    assign hv_o[17]=data_i[11];
    assign hv_o[18]=data_i[12];
    assign hv_o[19]=data_i[13];
    assign hv_o[20]=data_i[14];
    assign hv_o[21]=data_i[15];
    assign hv_o[22]=data_i[16];
    assign hv_o[23]=data_i[17];
    assign hv_o[24]=data_i[18];
    assign hv_o[25]=data_i[19];
    assign hv_o[26]=data_i[20];
    assign hv_o[27]=data_i[21];
    assign hv_o[28]=data_i[22];
    assign hv_o[29]=data_i[23];
    assign hv_o[30]=data_i[24];
    assign hv_o[31]=data_i[25];
        //Checkbits
    assign hv_o[0]=ocheck_int;
    assign hv_o[1]=hcheck_int[0];
    assign hv_o[2]=hcheck_int[1];
    assign hv_o[4]=hcheck_int[2];
    assign hv_o[8]=hcheck_int[3];
    assign hv_o[16]=hcheck_int[4];
    //compute checkbits
    assign hcheck_int[0] = ^{hv_o[3],hv_o[5],hv_o[7],
                            hv_o[9],hv_o[11],hv_o[13],hv_o[15],
                            hv_o[17],hv_o[19],hv_o[21],hv_o[23],
                            hv_o[25],hv_o[27],hv_o[29],hv_o[31]};

    assign hcheck_int[1] = ^{hv_o[3],hv_o[6],hv_o[7],
                            hv_o[10],hv_o[11],hv_o[14],hv_o[15],
                            hv_o[18],hv_o[19], hv_o[22],hv_o[23],
                            hv_o[26],hv_o[27], hv_o[30],hv_o[31] };


    assign hcheck_int[2] = ^{hv_o[5],hv_o[6],hv_o[7],
                            hv_o[12],hv_o[13],hv_o[14],hv_o[15],
                            hv_o[20],hv_o[21],hv_o[22],hv_o[23],
                            hv_o[28],hv_o[29],hv_o[30],hv_o[31]};
                            
    assign hcheck_int[3] = ^{hv_o[9],hv_o[10],hv_o[11],hv_o[12],hv_o[13],hv_o[14],hv_o[15],
                             hv_o[24],hv_o[25],hv_o[26],hv_o[27],hv_o[28],hv_o[29],hv_o[30],hv_o[31]};

    assign hcheck_int[4] = ^{hv_o[17],hv_o[18],hv_o[19],hv_o[20],hv_o[21],hv_o[22],hv_o[23],
                             hv_o[24],hv_o[25],hv_o[26],hv_o[27],hv_o[28],hv_o[29],hv_o[30],hv_o[31]};


    assign ocheck_int = ^hv_o[31:1];
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


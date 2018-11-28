//-----------------------------------------------------
// Design Name : decoder16
// File Name   : decoder16.sv
// Function    : decoder using assign
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module decoder16 (
input  wire [3:0]  binary_in   , //  4 bit binary input
output wire [15:0] decoder_out , //  16-bit out 
input  wire        enable        //  Enable for the decoder
);
//--------------Code Starts Here----------------------- 
assign decoder_out = (enable) ? (1 << binary_in) : 16'b0 ;

endmodule

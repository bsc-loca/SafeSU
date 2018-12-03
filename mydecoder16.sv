/-----------------------------------------------------
// Design Name : mydecoder16
// File Name   : mydecoder16.sv
// Function    : mydecoder using assign
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module mydecoder16 (
input  wire [3:0]  binary_in   , //  4 bit binary input
output wire [15:0] mydecoder_out , //  16-bit out 
input  wire        enable        //  Enable for the mydecoder
);
//--------------Code Starts Here----------------------- 
assign mydecoder_out = (enable) ? (1 << binary_in) : 16'b0 ;

endmodule

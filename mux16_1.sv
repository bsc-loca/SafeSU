//-----------------------------------------------------
// Design Name : mux16_1
// File Name   : mux16_1.sv
// Function    : Multiplexer using case
// Coder       : Guillem Cabo
//-----------------------------------------------------
module mux16_1 #(
parameter DATA_WIDTH = 64)
(
         input  wire[DATA_WIDTH-1:0]        in0            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in1            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in2            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in3            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in4            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in5            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in6            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in7            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in8            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in9            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in10            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in11            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in12            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in13            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in14            ,// signal  
         input  wire[DATA_WIDTH-1:0]        in15            ,// signal  
         input  wire[3:0]        sel             ,// signal  
         output wire[DATA_WIDTH-1:0]        out            // signal  
);
always @(*)
	begin
	      // Address decoding for reading registers
	      case (sel)
	        4'h00   : out = in0;
	        4'h01   : out = in1;
	        4'h02   : out = in2;
	        4'h03   : out = in3;
	        4'h04   : out = in4;
	        4'h05   : out = in5;
	        4'h06   : out = in6;
	        4'h07   : out = in7;
	        4'h08   : out = in8;
	        4'h09   : out = in9;
	        4'h0A   : out = in10;
	        4'h0B   : out = in11;
	        4'h0C   : out = in12;
	        4'h0D   : out = in13;
	        4'h0E   : out = in14;
	        4'h0F   : out = in15;
	        default : out = 0;
	      endcase
    end
endmodule

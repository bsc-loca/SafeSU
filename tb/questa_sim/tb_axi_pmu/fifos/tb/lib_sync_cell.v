//
// Model of a synchronisation cell
// (Rising edge to rising edge, two registers)
//
// Freeware September 2015, Fen Logic Ltd.
// This code is free and is delivered 'as is'.
// It comes without any warranty, to the extent permitted by applicable law.
// There are no restrictions to any use or re-use of this code
// in any form or shape. It would be nice if you keep my company name
// in the source or modified source code but even that is not
// required as I can't check it anyway.
// But the code comes with no warranties or guarantees whatsoever.
//

module lib_sync_cell (
  input      CLK,  
  input      CLRn,
  input      D,
  output reg Q
 );
 
 
`ifdef FIFO_SIM_ASYNC
// Simulate  a-synchronous behaviour:
// FFs will clock data in at a different time 

// Generate a random constant delay 
// in the range 0..15
time d;
initial
  d = $random() & 32'h00F;


reg delta;
   always @(D)
     delta <= #d D;
`endif

reg meta;
   always @(posedge CLK or negedge CLRn)
   begin
      if (!CLRn)
      begin
         meta <= 1'b0;
         Q    <= 1'b0;
      end
      else
      begin
`ifdef FIFO_SIM_ASYNC
         meta <= delta;
`else
         meta <= D;
`endif         
         Q    <= meta;
      end
   end  
endmodule   
//
//  A-synchronous FIFO level test
// 
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

module async_fifo_level_test;

localparam CLK_PERIOD=100;

localparam WI = 16;
localparam L2D= 4;

reg           clk;
reg           reset_n;

reg  [WI-1:0] w_data;
reg           w_strobe;
wire          w_full;
wire [L2D:0] w_level;

wire [WI-1:0] r_data;
reg           r_strobe;
wire          r_empty;
wire [L2D:0] r_level;


integer i,rnd,wt,rd;
integer wl,rl;


   initial
   begin

      reset_n   = 1'b0;
      w_strobe  = 1'b0;
      r_strobe  = 1'b0;
      w_data    = 16'h1234;
      wl=0;
      rl=0;

      #(CLK_PERIOD*10) ;
      @(posedge clk) #5;
      reset_n = 1'b1;
      #(CLK_PERIOD*4) ;
      for (i=0; i<1000000; i=i+1)
      begin
      	rnd = $random;

         wt=0;
      	if (rnd & 1)
      	begin
      		if (!w_full)
      		begin
               w_strobe =  1'b1;
               wt = 1;
            end
         end

         rd=0;
         if (rnd & 2)
         begin
         	if (!r_empty)
         	begin
               r_strobe =  1'b1;
               rd = 1;
            end
         end
         #CLK_PERIOD ;
         // One cycle later the effect of the read and write is present
         if (wt)
            wl = wl + 1;
         if (rd)
            rl =rl - 1;
         if (w_level!=wl)
         begin
         	$display("@%0t: Direct write level error",$time);
         	#10 $stop;
         end
         if (r_level!=rl)
         begin
         	$display("@%0t: Direct read level error",$time);
         	#10 $stop;
         end
         w_strobe =  1'b0;
         r_strobe =  1'b0;
         #CLK_PERIOD ;
         #CLK_PERIOD ;
         // two cycles later the effect of the 'other' port arrives
         if (rd)
            wl = wl - 1;
         if (wt)
            rl =rl + 1;
         if (w_level!=wl)
         begin
         	$display("@%0t: Delayed write level error",$time);
         	#10 $stop;
         end
         if (r_level!=rl)
         begin
         	$display("@%0t: Delayed read level error",$time);
         	#10 $stop;
         end
         #CLK_PERIOD ;
         #CLK_PERIOD ;

      end
      $display("FIFO level test passed");

      $stop;

   end


async_fifo
   #(
      .WI  (WI) ,
      .L2D (L2D)
   ) // parameters
async_fifo_inst (

      .reset_n (reset_n),

      .w_clk   (clk),
      .w_data  (w_data),
      .w_strobe(w_strobe),
      .w_full  (w_full),
      .w_level (w_level),

      .r_clk   (clk),
      .r_data  (r_data),
      .r_strobe(r_strobe),
      .r_empty (r_empty),
      .r_level (r_level)
   );



   // Generate clock. 
   initial
   begin
      clk = 1'b0;
      forever
         #(CLK_PERIOD/2) clk = ~clk;
   end

endmodule

//
//  A-synchronous FIFO with library cells test
// This behavioural test tries to shake out any a-synchtonisity errors. 
//
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

module async_fifo_lib_test;

localparam WCLK_PERIOD=208;
localparam RCLK_PERIOD=200;

localparam WI = 16;
localparam L2D= 4;
localparam LMAX = (1<<L2D);

reg           wclk;
reg           rclk;
reg           reset_n;

reg  [WI-1:0] w_data;
reg           w_strobe;
wire          w_full;
wire  [L2D:0] w_level;

wire [WI-1:0] r_data;
reg           r_strobe;
wire          r_empty;
wire  [L2D:0] r_level;


integer i;
reg   [WI-1:0] exp_r_data;


   initial
   begin

      reset_n   = 1'b0;

      #(WCLK_PERIOD*10) ;
      @(posedge wclk) #5;
      reset_n = 1'b1;
      #(WCLK_PERIOD*4) ;
      for (i=0; i<1000000; i=i+1)
         #(WCLK_PERIOD*40) ;
      
      $display("FIFO test passed");

      $stop;

   end


   always @(posedge wclk or negedge reset_n)
   begin
      if (!reset_n)
		begin
         w_strobe <=  1'b0;
         w_data   <= 0;
      end
      else
      begin
         w_strobe <=  1'b0;
         if ($random & 4)
      	begin
      		if (!w_full && !(w_level==LMAX-1 & w_strobe))
      		begin
               w_strobe <=  1'b1;
               w_data   <= w_data + 1;
            end
         end // do write
      end // clocked 
   end // always 

   always @(posedge rclk or negedge reset_n)
   begin
      if (!reset_n)
		begin
         r_strobe <=  1'b0;
         exp_r_data   <= 1;
      end
      else
      begin
         r_strobe   <=  1'b0;
         if ($random & 8)
         begin
         	if (!r_empty && !(r_level==1 & r_strobe))
               r_strobe   <=  1'b1;
         end // do read 
         
         if (r_strobe)
         begin
            exp_r_data <= exp_r_data + 1;
            if (exp_r_data!==r_data)
            begin
               $display("@%0t read mismatch. Have 0x%4X, expected 0x%04x",
                         $time,r_data,exp_r_data);
               #210 $stop;
            end
         end // was read 
      end // clocked 
   end // always 

async_fifo_lib
   #(
      .WI  (WI) ,
      .L2D (L2D)
   ) // parameters
async_fifo_lib_inst (

      .reset_n (reset_n),

      .w_clk   (wclk),
      .w_data  (w_data),
      .w_strobe(w_strobe),
      .w_full  (w_full),
      .w_level (w_level),

      .r_clk   (rclk),
      .r_data  (r_data),
      .r_strobe(r_strobe),
      .r_empty (r_empty),
      .r_level (r_level)
   );



   // Generate  clocks 
   initial
   begin
      wclk = 1'b0;
      forever
         #(WCLK_PERIOD/2) wclk = ~wclk;
   end
   initial
   begin
      rclk = 1'b0;
      forever
         #(RCLK_PERIOD/2) rclk = ~rclk;
   end

endmodule

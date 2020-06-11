//
//  Synchronous FIFO test
//  Half data width FIFO 
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

module sync_fifo_hd_test;

localparam CLK_PERIOD=100;

localparam WI = 8;
localparam DEPTH = 16;
localparam LEVLBITS = 5; // 0..16 

reg           clk;
reg           reset_n;
reg           enable;
reg           clear;

reg  [WI*2-1:0] wdata;
reg           write;

wire          empty;
wire          full ; 
wire [LEVLBITS-1:0]  level;

wire [WI-1:0] rdata;
reg           read;

integer i;
reg   [WI-1:0] exp_rdata;


   initial
   begin

      reset_n   = 1'b0;
      enable    = 1'b1;
      clear     = 1'b0;

      #(CLK_PERIOD*10) ;
      @(posedge clk) #5;
      reset_n = 1'b1;
      #(CLK_PERIOD*4) ;
      for (i=0; i<1000000; i=i+1)
         #(CLK_PERIOD*4) ;

      $display("FIFO test passed");

      $stop;

   end

sync_fifo_hd
   #(
      .WI      (WI) ,
      .DEPTH   (DEPTH),
      .LEVLBITS(LEVLBITS), 
      .REGFLAGS(1)  // !! Run test twice:REGFLAGS=0 & REGFLAGS=1
   ) // parameters
sync_fifo_hd_inst (
      .clk     (clk),
      .reset_n (reset_n),
      .enable  (enable),
      .clear   (clear),

      .wdata  (wdata),
      .write  (write),
      
      .rdata  (rdata),
      .read   (read),

      .full   (full),
      .empty  (empty),
      .level  (level)
   );

   always @(posedge clk or negedge reset_n)
   begin
      if (!reset_n)
		begin
         write <=  1'b0;
         wdata <=  16'hFFFE;  // 
      end
      else
      begin
         write <=  1'b0;
         if ($random & 8)
      	begin
      		if (!full && !(level<DEPTH-1 & write))
      		begin
               write <=  1'b1;
               wdata[7:0]  <= wdata[ 7:0] + 2;
               wdata[15:8] <= wdata[15:8] + 2;
            end
         end // do write
      end // clocked 
   end // always 

   always @(posedge clk or negedge reset_n)
   begin
      if (!reset_n)
		begin
         read <=  1'b0;
         exp_rdata   <= 0;
      end
      else
      begin
         read   <=  1'b0;
         if ($random & 3)
         begin
         	if (!empty && !(level==1 & read))
               read   <=  1'b1;
         end // do read 
         
         if (read)
         begin
            exp_rdata <= exp_rdata + 1;
            if (exp_rdata!==rdata)
            begin
               $display("@%0t read FIFO mismatch. Have 0x%04X, expected 0x%04x",
                         $time,rdata,exp_rdata);
               #210 $stop;
            end
         end // was read 
         
         if (full && level<=DEPTH-2)
         begin
            $display("@%0t Full too early",
                      $time,rdata,exp_rdata);
            #210 $stop;
         end
         if (empty && level!=0)
         begin
            $display("@%0t Empty too early",
                      $time,rdata,exp_rdata);
            #210 $stop;
         end
         
              
      end // clocked 
   end // always 


   // Generate clock
   initial
   begin
      clk = 1'b0;
      forever
         #(CLK_PERIOD/2) clk = ~clk;
   end

endmodule

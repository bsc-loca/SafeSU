//
// AXI master cycles generator
///
// Design by G.J. van Loo, FenLogic Ltd, October-2017.
//
// This program is free software. It comes without any guarantees or
// warranty to the extent permitted by applicable law. Although the
// author has attempted to find and correct any bugs in this free software
// program, the author is not responsible for any damage or losses of any
// kind caused by the use or misuse of the program. You can redistribute
// the program and or modify it in any form without obligations, but the
// author would appreciated if these credits stays in.
//
// This AXI test master has been developed alongside the axi_mux code.
// As with most big test benches I had to balance the time spend on
// the test bench versus the actual code being tested. Therefore this
// test bench is not complete:
// No support for user signals
// No support for response delays
// No support for write response matching 
// Not checking the reponse IDs
// 
// For operating an usage details read the manual. 
// 
`timescale 1 ns / 1 ps

module axi_test_master 
#( parameter ADRS_BITS = 32,
             DATA_BITS = 32,
             LEN_BITS  = 4,
             ID_BITS   = 6,
             // Depth of the queues (FIFOs)
             AQ_DEPTH  = 10, // Max 1K addresses
             DQ_DEPTH  = 16  // Max 64K data 
 )             
(
   input  clk,
   input  reset_n,
   input  run,
   output done,

   //
   // Write ports   
   //
   
   // Write address
   output reg               awvalid , 
   input                    awready , 
   output   [ADRS_BITS-1:0] awaddr  , 
   output    [LEN_BITS-1:0] awlen   , 
   output            [ 2:0] awsize  , 
   output     [ID_BITS-1:0] awid    , 
   output            [ 1:0] awburst , 
   // Unsupported ports (0)
   output            [ 3:0] awcache , 
   output            [ 1:0] awlock  , 
   output            [ 2:0] awprot  , 
   output            [ 3:0] awqos   , 
                           
   // write data           
   output reg               wvalid  , 
   input                    wready  , 
   output   [DATA_BITS-1:0] wdata   , 
   output [DATA_BITS/8-1:0] wstrb   , 
   output                   wlast   , 
   output     [ID_BITS-1:0] wid     , 

   // write response    
   input                    bvalid  , 
   output                   bready  , 
   input            [ 1 :0] bresp   , 
   input      [ID_BITS-1:0] bid     ,
   
   //
   // Read ports
   //
   
   // Read address 
   output reg               arvalid, 
   input                    arready, 
   output   [ADRS_BITS-1:0] araddr , 
   output     [ID_BITS-1:0] arid   , 
   output    [LEN_BITS-1:0] arlen  , 
   output             [2:0] arsize , 
   output             [1:0] arburst, 
   // Unsupported ports (0)
   output             [3:0] arcache, 
   output             [1:0] arlock , 
   output             [2:0] arprot , 
   output             [3:0] arqos  , 

   // Read Data
   input                    rvalid , 
   output                   rready , 
   input    [DATA_BITS-1:0] rdata  , 
   input                    rlast  , 
   input     [ID_BITS-1 :0] rid    ,
   input            [ 1 :0] rresp   
   
);   

   assign awcache = 4'b0; 
   assign awlock  = 2'b0; 
   assign awprot  = 3'b0; 
   assign awqos   = 4'b0; 
   
   // Not checking bresponse ID/code yet
   assign bready = 1'b1;

   // read response id is checked
   // use axi_test_master.rid_check_on=0 to disable (but why should you?)
reg rid_check_on = 1'b1;



  /***********************************************************\
   *      _    _      _ _          ___      _                *
   *     | |  | |    (_) |        / _ \    | |               *
   *     | |  | |_ __ _| |_ ___  / /_\ \ __| |_ __ ___       *
   *     | |/\| | '__| | __/ _ \ |  _  |/ _` | '__/ __|      *
   *     \  /\  / |  | | ||  __/ | | | | (_| | |  \__ \      *
   *      \/  \/|_|  |_|\__\___| \_| |_/\__,_|_|  |___/      *
   *                                                         *
  \***********************************************************/
  
// Write address FIFO holds: 
//    awaddr : ADRS_BITS
//    awlen  : LEN_SIZE
//    awsize : 3
//    awid   : ID_BITS
//    awburst: 2
// 
// Omitted (tied off) are: 
//    awcache: 4 
//    awlock : 2
//    awprot : 3
//    awqos  : 4

localparam AW_WIDTH = ADRS_BITS+LEN_BITS+3+ID_BITS+2;

reg                 awff_write;
reg  [AW_WIDTH-1:0] awff_wdata;
wire                awff_read;
wire [AW_WIDTH-1:0] awff_rdata;
wire                awff_full;
wire                awff_empty;
wire   [AQ_DEPTH:0] awff_level;


 sync_fifo
#(.WIDTH(AW_WIDTH),     // width in bits
   .L2D(AQ_DEPTH),  // Log 2 Depth, 5=32 deep
   .REGFLAGS(0)         // Full, empty are registered
)
aw_fifo
(
   .clk    (clk      ),   // system clock                 
   .reset_n(reset_n  ), // A-synchronous low reset/clear
   .enable (1'b1     ), // clock gating                 
   .clear  (1'b0     ), // Synchronous clear            
                                            
   .write  (awff_write), // write FIFO                   
   .wdata  (awff_wdata), // write data                   
   .read   (awff_read ), // read FIFO                    
   .rdata  (awff_rdata), // read data                    
         
   .empty  (awff_empty), // FIFO is empty                
   .full   (awff_full ), // FIFO is full                 
   .level  (awff_level)  // Fill level                   
);

   // Split AW fifo output in fields   
   assign {
    awaddr  , 
    awlen   , 
    awsize  , 
    awid    , 
    awburst 
   } = awff_rdata;   

//
// Delay & sync have their own FIFO
// as we need it one cycle ahead of the axi data 
// 
reg  [8:0] awdff_wdata;
wire       awdff_read;
wire [8:0] awdff_rdata;
wire       awdff_empty;
 
wire [ 7:0] aw_delay;
wire        aw_sync;
reg         aw_wait_sync;

// These belong to the write data control but
// are used in address FSM below 
wire        w_sync;  
wire        wff_empty;
reg         w_wait_sync;
wire        wdff_empty;

//
sync_fifo
#(.WIDTH(9),     // width in bits
   .L2D(AQ_DEPTH),  // Log 2 Depth, 5=32 deep
   .REGFLAGS(0)         // Full, empty are registered
)
aw_delay_fifo
(
   .clk    (clk      ),   // system clock                 
   .reset_n(reset_n  ), // A-synchronous low reset/clear
   .enable (1'b1     ), // clock gating                 
   .clear  (1'b0     ), // Synchronous clear            
                                            
   .write  (awff_write), // write FIFO                   
   .wdata  (awdff_wdata), // write data                   
   .read   (awdff_read ), // read FIFO                    
   .rdata  (awdff_rdata), // read data                    
         
   .empty  (awdff_empty), // FIFO is empty                
   .full   (), // FIFO is full                 
   .level  ()  // Fill level                   
);
   assign {aw_sync,aw_delay} = awdff_rdata;
   
//
// Put a write address in the FIFO
//
task q_wadrs;
input integer address;
input integer length;
input integer size;
input integer id;
input integer burst;
input integer delay_random;
input integer delay;
reg [7:0] out_delay;
begin
   // If full and not running risc of blocking is great
   // (unless somebosy used a fork) 
   if (awff_full)
   begin
      if (!run)
      begin
         $display("%m: AW FIFO is full. Stopping...");
         #1 $stop;
      end
      else
      begin
         while (awff_full)
            @(posedge clk);
      end
   end
   
   if (delay_random)
      out_delay = $random % delay;
    else
      out_delay = delay;
  
   // Convert size if so required
   // Everything below 8 is assumed to have the
   // real AXI format already 
   case (size)
      8 : size = 0;
     16 : size = 1;
     32 : size = 2;
     64 : size = 3;
    128 : size = 4;
    256 : size = 5;
    512 : size = 6;
   1024 : size = 7;
   default : if (size<0 || size>7)
             begin
                $display("%m: Illegal size. Stopping...");
                $stop;
             end
   endcase
   // Convert from user to AXI length 
   length = length-1;
        
   awff_wdata = {address[ADRS_BITS-1:0],
                 length[LEN_BITS-1:0],
                 size[2:0],
                 id[ID_BITS-1:0],
                 burst[1:0]};
   awdff_wdata = {1'b0,out_delay};
   @(negedge clk)                  
      awff_write <= 1'b1; 
   @(posedge clk)                  
      #1 awff_write <= 1'b0; 

end
endtask


reg [7:0] aw_delay_count;

  always @(posedge clk or negedge reset_n)
   begin
      if (!reset_n)
      begin
         awvalid        <= 1'b0;
         aw_delay_count <= 8'h00;
         aw_wait_sync   <= 1'b0;
      end
      else
      begin
              
        if (run)
        begin
        
            // Are we running a cycle?
            if (awvalid)
            begin
               // Does it finish?
               if (awready)
               begin
                  // check FIFO what to do next                 
                  if (awff_level==1) // or awdff_empty... 
                     // We are using the bottom entry: stop 
                     awvalid <= 1'b0; // Nothing 
                  else
                  begin
                     // FIFO output is valid
                     aw_delay_count <= aw_delay; 
                     
                     // Do we have a synced cycle?
                     if (aw_sync)
                     begin
                        // If write is witing for async 
                        // or write happens to finish AND it has a sync
                        // we can continue)
                        if (w_wait_sync | (wvalid & wready & wlast & (!wdff_empty & w_sync)))
                        begin
                           if (aw_delay==0)
                              // Output data now  
                              awvalid <= 1'b1;
                           else
                              awvalid <= 1'b0;
                        end
                        else
                        begin
                          // Wait for write sync cycle 
                           awvalid <= 1'b0;
                           aw_wait_sync <= 1'b1;
                        end
                     end
                     else
                     begin // No sync cyle
                        if (aw_delay==0)
                           // Output data now  
                           awvalid <= 1'b1;
                        else
                           awvalid <= 1'b0;
                     end

                  end // FF has data 
               end // if awready
               // Else continue waiting for ready 
            end // running cycle 
            else
            begin
               // No awvalid,
               // Are we waiting for sync?
               if (aw_wait_sync)
               begin
                 // Do we have a write sync?
                  if (wvalid & wready & wlast & (!wdff_empty & w_sync))
                  begin
                     aw_wait_sync <= 1'b0;
                     if (aw_delay==0)
                        // Output data now  
                        awvalid <= 1'b1;
                     else
                        awvalid <= 1'b0;
                  end 
                  else
                     if (wff_empty)
                     begin
                        $display("%m, AW is waiting for sync that can't come");
                        #1 $stop;
                     end
               end
               else
               begin
                  // Are we running a delay?
                  if (aw_delay_count!=0)
                  begin
                     aw_delay_count <= aw_delay_count - 1;
                     // Is the delay over?
                     if (aw_delay_count==1)
                        awvalid <= 1'b1;
                  end  // running delay 
                  else
                  begin
                     // Has the FIFO something?
                     if (!awff_empty)
                     begin
                        aw_delay_count <= aw_delay; 
                        if (aw_delay==0)
                           // Output data now  
                           awvalid <= 1'b1;
                        else
                           awvalid <= 1'b0;
                    end // nothing in FIFO
                  end // no delay
               end // no sync
            end // no valid
        end // run
        else
           awvalid <= 1'b0;
           
      end // clocked 
   end // always 
   
   assign awff_read  = awvalid & awready;
   
   // awdff_read is high for every case where awvalid <= 1:
   // The following monster expression has been built by 
   // following the above code and extracting all the paths 
   // which lead to awvalid <= 1:
   assign awdff_read =
   run & ((awvalid & awready & (awff_level!=1) & 
             ( 
                (aw_sync & 
                    (w_wait_sync | (wvalid & wready & wlast & (!wdff_empty & w_sync)))
                      & (aw_delay==0)
                )
                |
                (!aw_sync & aw_delay==0)
                )
            ) // awvalid 
          |
          (!awvalid &  
             (
                (aw_wait_sync &
                  (wvalid & wready & wlast & (!wdff_empty & w_sync) & 
                   (aw_delay==0))
                ) // sync 
                |
                (!aw_wait_sync & ((aw_delay_count==1) | 
                                 (!awff_empty& (aw_delay==0)))
                ) // !sync
             )
           )
         ); 
   // To check the expression awff_read should follow awdff_read
   // by one clock cycle if awready is always high 
    
 

  // Repeat all of the above for write data 

  /********************************************************\
   *     _    _      _ _        ______      _             *
   *    | |  | |    (_) |       |  _  \    | |            *
   *    | |  | |_ __ _| |_ ___  | | | |__ _| |_ __ _      *
   *    | |/\| | '__| | __/ _ \ | | | / _` | __/ _` |     *
   *    \  /\  / |  | | ||  __/ | |/ / (_| | || (_| |     *
   *     \/  \/|_|  |_|\__\___| |___/ \__,_|\__\__,_|     *
   *                                                      *
  \********************************************************/

//    wdata : DATA_BITS
//    wstrb : DATA_BITS/8 bits
//    wlast : 1
//    wid   : ID_BITS
// 
// +2 as it also holds sync_mode 
localparam W_WIDTH = DATA_BITS+DATA_BITS/8+1+ID_BITS;

reg                wff_write;
reg  [W_WIDTH-1:0] wff_wdata;
wire               wff_read;
wire [W_WIDTH-1:0] wff_rdata;
wire               wff_full;
wire  [DQ_DEPTH:0] wff_level;

//wire  w_sync;


 sync_fifo
#(.WIDTH(W_WIDTH),      // width in bits
   .L2D(DQ_DEPTH),  // Log 2 Depth, 5=32 deep
   .REGFLAGS(0)         // Full, empty are registered
)
w_fifo
(
   .clk    (clk      ),   // system clock                 
   .reset_n(reset_n  ), // A-synchronous low reset/clear
   .enable (1'b1     ), // clock gating                 
   .clear  (1'b0     ), // Synchronous clear            
                                            
   .write  (wff_write), // write FIFO                   
   .wdata  (wff_wdata), // write data                   
   .read   (wff_read ), // read FIFO                    
   .rdata  (wff_rdata), // read data                    
         
   .empty  (wff_empty), // FIFO is empty                
   .full   (wff_full ), // FIFO is full                 
   .level  (wff_level)  // Fill level                   
);

  // Split W fifo output in fields   
   assign {
    wdata , 
    wstrb , 
    wlast , 
    wid   
   } = wff_rdata;   
 
//
// Delay has it's own FIFO
// as we need it one cycle ahead of the axi data 
// 
reg  [8:0] wdff_wdata;
wire       wdff_read;
wire [8:0] wdff_rdata;
 
wire [ 7:0] w_delay;

//
sync_fifo
#(.WIDTH(9),     // width in bits
   .L2D(DQ_DEPTH),  // Log 2 Depth, 5=32 deep
   .REGFLAGS(0)         // Full, empty are registered
)
w_delay_fifo
(
   .clk    (clk      ),   // system clock                 
   .reset_n(reset_n  ), // A-synchronous low reset/clear
   .enable (1'b1     ), // clock gating                 
   .clear  (1'b0     ), // Synchronous clear            
                                            
   .write  (wff_write), // write FIFO                   
   .wdata  (wdff_wdata), // write data                   
   .read   (wdff_read ), // read FIFO                    
   .rdata  (wdff_rdata), // read data                    
         
   .empty  (wdff_empty), // FIFO is empty                
   .full   (), // FIFO is full                 
   .level  ()  // Fill level                   
);

   assign {w_sync,w_delay} = wdff_rdata;

//
// Put write data in the FIFO
//
// TODO: Support more then 1 unit?
//
task q_wdata;
input integer data;
input integer strobes;
input integer last;
input integer id;
input integer delay_random;
input integer delay;
reg [7:0] out_delay;
begin
   // If full and not running risc of blocking is great
   // (unless somebosy used a fork) 
   if (wff_full)
   begin
      if (!run)
      begin
         $display("%m: W FIFO is full. Stopping...");
         $stop;
      end
      else
      begin
         while (wff_full)
            @(posedge clk);
      end
   end
      
   if (delay_random)
      out_delay = $random % delay;
    else
      out_delay = delay;
          
   wff_wdata = {data[DATA_BITS-1:0],
                strobes[DATA_BITS/8-1:0],
                last[0],
                id[ID_BITS-1:0]}; // sync mode 
   wdff_wdata = {1'b0,out_delay};
   @(negedge clk)                  
      wff_write <= 1'b1; 
   @(posedge clk)                  
      #1 wff_write <= 1'b0; 

end
endtask


reg [7:0] w_delay_count;

  always @(posedge clk or negedge reset_n)
   begin
      if (!reset_n)
      begin
         wvalid        <= 1'b0;
         w_delay_count <= 8'h00;
         w_wait_sync   <= 1'b0;
      end
      else
      begin
              
        if (run)
        begin
        
            // Are we running a cycle?
            if (wvalid)
            begin
               // Does it finish?
               if (wready)
               begin
                  // check FIFO what to do next                 
                  if (wff_level==1) // or wdff_empty... 
                     // We are using the bottom entry: stop 
                     wvalid <= 1'b0; // Nothing 
                  else
                  begin
                     // FIFO output is valid
                     w_delay_count <= w_delay; 
                     
                     // Do we have a synced cycle?
                     if (w_sync)
                     begin
                        // If address is waiting for sync or 
                        // address happens to finish AND it has a sync
                        // we can continue)
                        if (aw_wait_sync | (awvalid & awready & (!awdff_empty & aw_sync)))
                        begin
                           if (w_delay==0)
                              // Output data now  
                              wvalid <= 1'b1;
                           else
                              wvalid <= 1'b0;
                        end
                        else
                        begin
                          // Wait for write sync cycle 
                           wvalid <= 1'b0;
                           w_wait_sync <= 1'b1;
                        end
                     end
                     else
                     begin // No sync cyle
                        if (w_delay==0)
                           // Output data now  
                           wvalid <= 1'b1;
                        else
                           wvalid <= 1'b0;
                     end

                  end // FF has data 
               end // have wready   
               // Else continue waiting for ready
            end // running cycle 
            else
            begin
               // No wvalid,
               // Are we waiting for sync?
               if (w_wait_sync)
               begin
                 // Do we have an address sync?
                  if (awvalid & awready & (!awdff_empty & aw_sync))
                  begin
                     w_wait_sync <= 1'b0;
                     if (w_delay==0)
                        // Output data now  
                        wvalid <= 1'b1;
                     else
                        wvalid <= 1'b0;
                  end 
                  else
                     if (awff_empty)
                     begin
                        $display("%m, W is waiting for sync that can't come");
                        #1 $stop;
                     end
               end
               else
               begin
                  // Are we running a delay?
                  if (w_delay_count!=0)
                  begin
                     w_delay_count <= w_delay_count - 1;
                     // Is the delay over?
                     if (w_delay_count==1)
                        wvalid <= 1'b1;
                  end  // running delay 
                  else
                  begin
                     // Has the FIFO something?
                     if (!wff_empty)
                     begin
                        w_delay_count <= w_delay; 
                        if (w_delay==0)
                           // Output data now  
                           wvalid <= 1'b1;
                        else
                           wvalid <= 1'b0;
                     end // nothing in FIFO
                  end // no delay
               end // no valid
            end //
        end // run
        else
           wvalid <= 1'b0;
           
      end // clocked 
   end // always 

   
   assign wff_read  = wvalid & wready;
   // wdff_read is high for every case where wvalid <= 1'b1;
   // The following monster expression has been built by 
   // following the above code and extracting all the paths 
   // which lead to avalid <= 1:
   assign wdff_read = 
      run & ( (wvalid & wready & (wff_level!=1) & 
                    ( (w_sync & 
                          (aw_wait_sync | (awvalid & awready & (!awdff_empty & aw_sync)))
                           & (w_delay==0)
                       )
                       |
                       ( !w_sync & (w_delay==0)
                       )
                    )
              ) // wvalid 
              |
              (!wvalid & 
                  ( 
                     (w_wait_sync & awvalid & awready & (!awdff_empty & aw_sync) &
                         (w_delay==0)
                     )
                     |
                     (!w_wait_sync & ((w_delay_count==1) | (!wff_empty& (w_delay==0)))
                     )
                  )
              ) // !wvalid
            );
   // To check the expression wff_read should follow wdff_read
   // by one clock cycle if wready is always high 
        
//    
// Put a synced write in the FIFOs
// For now only one data unit suppported 
//
task q_wsync;
input integer address;
input integer length;
input integer size;
input integer id;
input integer burst;
input integer adelay_random;
input integer adelay;

input integer data;
input integer strobes;
input integer last;
input integer wdelay_random;
input integer wdelay;
reg [7:0] out_adelay;
reg [7:0] out_wdelay;
begin
   // If full and not running risc of blocking is great
   // (unless somebosy used a fork) 
   if (awff_full | wff_full)
   begin
      if (!run)
      begin
         $display("%m: AW or W FIFO is full. Stopping...");
         #1 $stop;
      end
      else
      begin
         while (awff_full | wff_full)
            @(posedge clk);
      end
   end
   
   if (adelay_random)
      out_adelay = $random % adelay;
    else
      out_adelay = adelay;
  
   // Convert size if so required
   // Everything below 8 is assumed to have the
   // real AXI format already 
   case (size)
      8 : size = 0;
     16 : size = 1;
     32 : size = 2;
     64 : size = 3;
    128 : size = 4;
    256 : size = 5;
    512 : size = 6;
   1024 : size = 7;
   default : if (size<0 || size>7)
             begin
                $display("%m: Illegal size. Stopping...");
                $stop;
             end
   endcase
   // Convert from user to AXI length 
   length = length-1;
        
   awff_wdata = {address[ADRS_BITS-1:0],
                 length[LEN_BITS-1:0],
                 size[2:0],
                 id[ID_BITS-1:0],
                 burst[1:0]};
   awdff_wdata = {1'b1,out_adelay};

   if (wdelay_random)
      out_wdelay = $random % wdelay;
    else
      out_wdelay = wdelay;
          
   wff_wdata = {data[DATA_BITS-1:0],
                strobes[DATA_BITS/8-1:0],
                last[0],
                id[ID_BITS-1:0]}; // sync mode 
   wdff_wdata = {1'b1,out_wdelay};


   @(negedge clk)                  
      {wff_write,awff_write} <= 2'b11; 
   @(posedge clk)                  
      #1 {wff_write,awff_write} <= 2'b00; 

end
endtask

   
  /*********************************************************\
   *    ______               _    ___      _               *
   *    | ___ \             | |  / _ \    | |              *
   *    | |_/ /___  __ _  __| | / /_\ \ __| |_ __ ___      *
   *    |    // _ \/ _` |/ _` | |  _  |/ _` | '__/ __|     *
   *    | |\ \  __/ (_| | (_| | | | | | (_| | |  \__ \     *
   *    \_| \_\___|\__,_|\__,_| \_| |_/\__,_|_|  |___/     *
   *                                                       *
  \*********************************************************/

   assign arcache = 4'b0; 
   assign arlock  = 2'b0; 
   assign arprot  = 3'b0; 
   assign arqos   = 4'b0; 
   
// Read address FIFO holds: 
//    araddr : ADRS_BITS
//    arlen  : LEN_SIZE
//    arsize : 3
//    arid   : ID_BITS
//    arburst: 2
// 
// Omitted (tied off) are: 
//    arcache: 4 
//    arlock : 2
//    arprot : 3
//    arqos  : 4

localparam AR_WIDTH = ADRS_BITS+LEN_BITS+3+ID_BITS+2;

reg                 arff_write;
reg  [AR_WIDTH-1:0] arff_wdata;
wire                arff_read;
wire [AR_WIDTH-1:0] arff_rdata;
wire                arff_full;
wire                arff_empty;
wire   [AQ_DEPTH:0] arff_level;


 sync_fifo
#(.WIDTH(AR_WIDTH),     // width in bits
   .L2D(AQ_DEPTH),  // Log 2 Depth, 5=32 deep
   .REGFLAGS(0)         // Full, empty are registered
)
ar_fifo
(
   .clk    (clk      ),   // system clock                 
   .reset_n(reset_n  ), // A-synchronous low reset/clear
   .enable (1'b1     ), // clock gating                 
   .clear  (1'b0     ), // Synchronous clear            
                                            
   .write  (arff_write), // write FIFO                   
   .wdata  (arff_wdata), // write data                   
   .read   (arff_read ), // read FIFO                    
   .rdata  (arff_rdata), // read data                    
         
   .empty  (arff_empty), // FIFO is empty                
   .full   (arff_full ), // FIFO is full                 
   .level  (arff_level)  // Fill level                   
);

   // Split AR fifo output in fields   
   assign {
    araddr  , 
    arlen   , 
    arsize  , 
    arid    , 
    arburst 
   } = arff_rdata;   

//
// Delay has its own FIFO
// as we need it one cycle ahead of the axi data 
// The read address bus has no need for sync!
// 
reg  [7:0] ardff_wdata;
wire       ardff_read;
wire [7:0] ardff_rdata;
wire       ardff_empty;
 
wire [ 7:0] ar_delay;

//
sync_fifo
#(.WIDTH(8),     // width in bits
   .L2D(AQ_DEPTH),  // Log 2 Depth, 5=32 deep
   .REGFLAGS(0)         // Full, empty are registered
)
ar_delay_fifo
(
   .clk    (clk      ),   // system clock                 
   .reset_n(reset_n  ), // A-synchronous low reset/clear
   .enable (1'b1     ), // clock gating                 
   .clear  (1'b0     ), // Synchronous clear            
                                            
   .write  (arff_write), // write FIFO                   
   .wdata  (ardff_wdata), // write data                   
   .read   (ardff_read ), // read FIFO                    
   .rdata  (ardff_rdata), // read data                    
         
   .empty  (ardff_empty), // FIFO is empty                
   .full   (), // FIFO is full                 
   .level  ()  // Fill level                   
);
   assign {ar_delay} = ardff_rdata; // Leave for ocmpatible reasons
   
//
// Put a read address in the FIFO
//
task q_radrs;
input integer address;
input integer length;
input integer size;
input integer id;
input integer burst;
input integer delay_random;
input integer delay;
reg [7:0] out_delay;
begin
   // If full and not running risc of blocking is great
   // (unless somebosy used a fork) 
   if (arff_full)
   begin
      if (!run)
      begin
         $display("%m: AR FIFO is full. Stopping...");
         #1 $stop;
      end
      else
      begin
         while (arff_full)
            @(posedge clk);
      end
   end
   
   if (delay_random)
      out_delay = $random % delay;
    else
      out_delay = delay;
  
   // Convert size if so required
   // Everything below 8 is assumed to have the
   // real AXI format already 
   case (size)
      8 : size = 0;
     16 : size = 1;
     32 : size = 2;
     64 : size = 3;
    128 : size = 4;
    256 : size = 5;
    512 : size = 6;
   1024 : size = 7;
   default : if (size<0 || size>7)
             begin
                $display("%m: Illegal size. Stopping...");
                $stop;
             end
   endcase
   // Convert from user to AXI length 
   length = length-1;
        
   arff_wdata = {address[ADRS_BITS-1:0],
                 length[LEN_BITS-1:0],
                 size[2:0],
                 id[ID_BITS-1:0],
                 burst[1:0]};
   ardff_wdata = {out_delay};
   @(negedge clk)                  
      arff_write <= 1'b1; 
   @(posedge clk)                  
      #1 arff_write <= 1'b0; 

end
endtask


reg [7:0] ar_delay_count;

  always @(posedge clk or negedge reset_n)
   begin
      if (!reset_n)
      begin
         arvalid        <= 1'b0;
         ar_delay_count <= 8'h00;
      end
      else
      begin
              
        if (run)
        begin
        
            // Are we running a cycle?
            if (arvalid)
            begin
               // Does it finish?
               if (arready)
               begin
                  // check FIFO what to do next                 
                  if (arff_level==1) // or ardff_empty... 
                     // We are using the bottom entry: stop 
                     arvalid <= 1'b0; // Nothing 
                  else
                  begin
                     // FIFO output is valid
                     ar_delay_count <= ar_delay; 
                     
                     begin // No sync cyle
                        if (ar_delay==0)
                           // Output data now  
                           arvalid <= 1'b1;
                        else
                           arvalid <= 1'b0;
                     end

                  end // FF has data 
               end // if arready
               // Else continue waiting for ready 
            end // running cycle 
            else
            begin
               // No arvalid,
               begin // Not waiting for sync
                  // Are we running a delay?
                  if (ar_delay_count!=0)
                  begin
                     ar_delay_count <= ar_delay_count - 1;
                     // Is the delay over?
                     if (ar_delay_count==1)
                        arvalid <= 1'b1;
                  end  // running delay 
                  else
                  begin
                     // Has the FIFO something?
                     if (!arff_empty)
                     begin
                        ar_delay_count <= ar_delay; 
                        if (ar_delay==0)
                           // Output data now  
                           arvalid <= 1'b1;
                        else
                           arvalid <= 1'b0;
                    end // nothing in FIFO
                  end // no delay
               end // no sync
            end // no valid
        end // run
        else
           arvalid <= 1'b0;
           
      end // clocked 
   end // always 
   
   assign arff_read  = arvalid & arready;
   
   // ardff_read is high for every case where arvalid <= 1:
   // The following monster expression has been built by 
   // following the above code and extracting all the paths 
   // which lead to arvalid <= 1:
   // (Extra Strange format is becasue sync has been removed, the rest remained)
   assign ardff_read =
   run & ((arvalid & arready & (arff_level!=1) & 
                (ar_delay==0)
           ) // arvalid 
          |
          (!arvalid &  
             (
                (((ar_delay_count==1) | 
                 (!arff_empty& (ar_delay==0)))
                ) // !sync
             )
           )
         ); 
   // To check the expression arff_read should follow ardff_read
   // by one clock cycle if arready is always high 




  /********************************************************\
   *    ______               _  ______      _             *
   *    | ___ \             | | |  _  \    | |            *
   *    | |_/ /___  __ _  __| | | | | |__ _| |_ __ _      *
   *    |    // _ \/ _` |/ _` | | | | / _` | __/ _` |     *
   *    | |\ \  __/ (_| | (_| | | |/ / (_| | || (_| |     *
   *    \_| \_\___|\__,_|\__,_| |___/ \__,_|\__\__,_|     *
   *                                                      *
  \********************************************************/
  
//
// NOT!!! coping with out-of-order data returns yet
//  

//    rdata : DATA_BITS
//    rlast : 1
//    rid   : ID_BITS
//    delay : 8
//    delay_mode : 1
// 
localparam R_WIDTH = DATA_BITS+1+ID_BITS+8+1;

reg                rff_write;
reg  [R_WIDTH-1:0] rff_wdata;
wire               rff_read;
wire [R_WIDTH-1:0] rff_rdata;
wire               rff_empty;
wire               rff_full;
wire  [DQ_DEPTH:0] rff_level;

wire [DATA_BITS-1:0] i_rdata;
wire   [ID_BITS-1:0] i_rid;
wire                 i_rlast;

wire [7:0] r_delay;
wire       r_delay_mode;

 sync_fifo
#(.WIDTH(R_WIDTH),      // width in bits
   .L2D(DQ_DEPTH),  // Log 2 Depth, 5=32 deep
   .REGFLAGS(0)         // Full, empty are registered
)
r_fifo
(
   .clk    (clk      ),   // system clock                 
   .reset_n(reset_n  ), // A-synchronous low reset/clear
   .enable (1'b1     ), // clock gating                 
   .clear  (1'b0     ), // Synchronous clear            
                                            
   .write  (rff_write), // write FIFO                   
   .wdata  (rff_wdata), // write data                   
   .read   (rff_read ), // read FIFO                    
   .rdata  (rff_rdata), // read data                    
         
   .empty  (rff_empty), // FIFO is empty                
   .full   (rff_full ), // FIFO is full                 
   .level  (rff_level)  // Fill level                   
);

  // Split R fifo output in fields   
   assign {
    i_rdata , 
    i_rlast , 
    i_rid   ,
    r_delay,
    r_delay_mode
   } = rff_rdata;   
 
//
// Put read data in the FIFO
//
task q_rdata;
input integer data;
input integer last;
input integer id;
input integer delay_random;
input integer delay;
input integer delay_mode;
reg [7:0] out_rdelay;
begin
   // If full and not running risc of blocking is great
   // (unless somebosy used a fork) 
   if (rff_full)
   begin
      if (!run)
      begin
         $display("%m: R FIFO is full. Stopping...");
         $stop;
      end
      else
      begin
         while (rff_full)
            @(posedge clk);
      end
   end
      
   if (delay_random)
      out_rdelay = $random % delay;
   else
      out_rdelay = delay;
          
   rff_wdata = {data[DATA_BITS-1:0],
                last[0],
                id[ID_BITS-1:0],
                out_rdelay,
                delay_mode[0]                                
                }; 
   @(negedge clk)                  
      rff_write <= 1'b1; 
   @(posedge clk)                  
      #1 rff_write <= 1'b0; 

end
endtask


reg [7:0] r_delay_count;
reg       post_rpop;

integer b,err;

   always @(posedge clk or negedge reset_n)
   begin
      if (!reset_n)
      begin
         r_delay_count <= 8'h00;
         post_rpop     <= 1'b0;
      end
      else
      begin
         
         // Look at fifo after we read fro it
         // or after RUN is asserted
         post_rpop <= rff_read | !run;
              
              
         if (run)
         begin
            if (!rready)
            begin
               if (r_delay_count)
                  r_delay_count <= r_delay_count - 1;
            end
            else
            begin
               if (post_rpop && r_delay!=0)
                  r_delay_count <= r_delay;
            end
            
            if (rvalid & rready & !rff_empty)
            begin
               err=0;
               // Checking bit by bit. 
               // If expected bit = 'x' we do not check it 
               // Is there a faster way.
               // e.g. mask out all 'x' bits???
               for (b=0; b<DATA_BITS && !err; b=b+1)
                  if (i_rdata[b]!==1'bx)
                     if (i_rdata[b]!==rdata[b])
                       err = 1;
               
               if (err)
               begin
                  $display("%m@%0t: read verify error. Have 0x%08X, expected 0x%08X",
                     $time,rdata,i_rdata);
                  #1 $stop;
               end
//               else  $display("%m@%0t: read verify OK. Have 0x%08X, expected 0x%08X",$time,rdata,i_rdata);

               if (rid_check_on)
               begin
                  if (i_rid!==rid)
                  begin
                     $display("%m@%0t: read ID error. Have 0x%02X, expected 0x%02X",
                        $time,rid,i_rid);
                     #1 $stop;
                  end
               end

               
            end
         end // run 
         
      end // clocked 
   end // always 
   
   assign rff_read = rvalid & rready & !rff_empty;
   assign rready = run & ((!rff_empty & (r_delay==0)) || (r_delay_count<1));
   
 
        
//    
// Put a read with data in the FIFOs
//
task q_ardata;
input integer address;
input integer length;
input integer size;
input integer id;
input integer burst;
input integer adelay_random;
input integer adelay;

input integer data;
input integer last;
input integer rdelay_random;
input integer rdelay;
input integer rdelay_mode; // not yet used 
reg [7:0] out_adelay;
reg [7:0] out_rdelay;
begin
   // If full and not running risc of blocking is great
   // (unless somebosy used a fork) 
   if (arff_full | rff_full)
   begin
      if (!run)
      begin
         $display("%m: AR or R FIFO is full. Stopping...");
         #1 $stop;
      end
      else
      begin
         while (arff_full | rff_full)
            @(posedge clk);
      end
   end
   
   if (adelay_random)
      out_adelay = $random % adelay;
    else
      out_adelay = adelay;
  
   // Convert size if so required
   // Everything below 8 is assumed to have the
   // real AXI format already 
   case (size)
      8 : size = 0;
     16 : size = 1;
     32 : size = 2;
     64 : size = 3;
    128 : size = 4;
    256 : size = 5;
    512 : size = 6;
   1024 : size = 7;
   default : if (size<0 || size>7)
             begin
                $display("%m: Illegal size. Stopping...");
                $stop;
             end
   endcase
   // Convert from user to AXI length 
   length = length-1;
        
    arff_wdata = {address[ADRS_BITS-1:0],
                 length[LEN_BITS-1:0],
                 size[2:0],
                 id[ID_BITS-1:0],
                 burst[1:0]};
    ardff_wdata = {out_adelay};

   if (rdelay_random)
      out_rdelay = $random % rdelay;
   else
      out_rdelay = rdelay;
          
   rff_wdata = {data[DATA_BITS-1:0],
                last[0],
                id[ID_BITS-1:0],
                out_rdelay,
                rdelay_mode[0]                                
                }; 
   @(negedge clk)                  
      {arff_write,rff_write} <= 2'b11; 
   @(posedge clk)                  
      #1 {arff_write,rff_write} <= 2'b00; 

end
endtask

   
   assign done = awff_empty & wff_empty & arff_empty & rff_empty;
 
endmodule

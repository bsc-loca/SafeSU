/* -----------------------------------------------
* Project Name   : AXI_PMU research 
* File           : tb_AXI_PMU.v
* Organization   : Barcelona Supercomputing Center
* Author(s)      : Guillem cabo 
* Email(s)       : guillem.cabo@bsc.es
* References     : 
* -----------------------------------------------
* Revision History
*  Revision   | Author    | Commit     | Description
*  0.0        | G.cabo    | 2d256e60a  | WIP: test integration of MCCU with PMU
* -----------------------------------------------
*/

//-----------------------------------------------------
// Function   : Shows intended behaviour 
// Description: Unit tests, if this fails functionality is broken
`timescale 1 ns / 1 ns
`default_nettype none
`include "colors.vh"
//***Headers***
//***Test bench***
module tb_AXI_PMU();
//***Parameters***
    parameter CLK_PERIOD      = 2;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
    parameter  VERBOSE = 0;
// Depth of the queues (FIFOs) for the axi_test_master
    parameter AQ_DEPTH  = 10; // Max 1K addresses
    parameter DQ_DEPTH  = 16;  // Max 64K data 
    parameter LEN_BITS  = 4;  
    parameter ID_BITS  = 1;   
//***DUT parameters***    
    parameter TB_DATA_WIDTH = 32;
    //parameter TB_ADDR_WIDTH = 7;
    parameter TB_ADDR_WIDTH = 32;
    parameter TB_WEIGHTS_WIDTH = 7;
    parameter TB_N_CORES = 1;
    parameter TB_CORE_EVENTS = 1;
//***local parameters to acces memory regions of peripheral***    
    //Get memory ranges of the different regions of the PMU
        //boundaries
    localparam first_addr =32'h00000;
    localparam n_registers = dut_AXI_PMU.inst_AXI_PMU.TOTAL_REGS; 
    localparam last_addr = first_addr+(n_registers-1)*4;
        //Counters addresses
    localparam base_counters = first_addr;
    localparam last_counter = first_addr + (dut_AXI_PMU.inst_AXI_PMU.N_COUNTERS-1)*4;
        //Conf_regs addresses
    localparam base_conf = last_counter + 4 ;
    localparam last_conf = base_conf + (dut_AXI_PMU.inst_AXI_PMU.N_CONF_REGS-1)*4;
    localparam main_conf = base_conf;
        //Overflow registers
    localparam n_overflow = dut_AXI_PMU.inst_AXI_PMU.N_OVERFLOW_REGS;
    localparam base_overflow = last_conf + 4;
    localparam last_overflow = base_overflow + (n_overflow-1)*4;
        //Quota 
    localparam n_quota = dut_AXI_PMU.inst_AXI_PMU.N_QUOTA_MASK 
                        + dut_AXI_PMU.inst_AXI_PMU.N_QUOTA_LIMIT;
    localparam base_quota = last_overflow + 4;
    localparam last_quota = base_quota + (n_quota-1) * 4;
    localparam first_quota_mask = base_quota; 
    localparam first_quota_limit = base_quota + (dut_AXI_PMU
                                                 .inst_AXI_PMU
                                                 .N_QUOTA_MASK -1)*4; 
        //MCCU
    localparam n_MCCU = dut_AXI_PMU.inst_AXI_PMU.MCCU_REGS;
    localparam n_cores_MCCU = dut_AXI_PMU.inst_AXI_PMU.MCCU_N_CORES;
    localparam base_MCCU = last_quota + 4;
    localparam last_MCCU = base_MCCU + (n_MCCU-1) *4;
    localparam main_MCCU_cfg = base_MCCU;
    localparam first_MCCU_quota = base_MCCU+4;
    localparam first_MCCU_weights = first_MCCU_quota 
                                    + (n_cores_MCCU-1)*4;
    localparam n_regs_MCCU_weights = dut_AXI_PMU.inst_AXI_PMU.MCCU_WEIGHTS_REGS;
    localparam first_MCCU_out_quota = first_MCCU_weights 
                                    + (n_regs_MCCU_weights-1)*4;
//***Signals***
    reg     tb_clk_i ;
    reg     tb_rstn_i ;
    reg     tb_EV0_i;
    reg     tb_EV1_i;
    reg     tb_EV2_i;
    reg     tb_EV3_i;
    reg     tb_EV4_i;
    reg     tb_EV5_i;
    reg     tb_EV6_i;
    reg     tb_EV7_i;
    reg     tb_EV8_i;
    reg     tb_EV9_i;
    reg     tb_EV10_i;
    reg     tb_EV11_i;
    reg     tb_EV12_i;
    reg     tb_EV13_i;
    reg     tb_EV14_i;
    reg     tb_EV15_i;
    wire    int_overflow_o;
    wire    int_quota_o;
    wire    int_quota_c0_o;
    wire    int_quota_c1_o;
//***Interfaces
    //AXI_LITE PORT
      // write address 
    wire                   tb_aw_valid ; 
    wire                   tb_aw_ready ; 
    wire   [TB_ADDR_WIDTH-1:0] tb_aw_addr  ; 
    wire    [LEN_BITS-1:0] tb_aw_len   ; 
    wire            [ 2:0] tb_aw_size  ; 
    wire     [ID_BITS-1:0] tb_aw_id    ; 
    wire            [ 1:0] tb_aw_burst ; 
    wire            [ 3:0] tb_aw_cache ; 
    wire            [ 1:0] tb_aw_lock  ; 
    wire            [ 2:0] tb_aw_prot  ; 
    wire            [ 3:0] tb_aw_qos   ; 
       // write data           
    wire                   tb_w_valid  ; 
    wire                   tb_w_ready  ; 
    wire   [TB_DATA_WIDTH-1:0] tb_w_data   ; 
    wire            [ 3:0] tb_w_strb   ; 
    wire                   tb_w_last   ; 
    wire     [ID_BITS-1:0] tb_w_id     ; 
       // write response    
    wire                   tb_b_valid  ; 
    wire                   tb_b_ready  ; 
    wire           [ 1 :0] tb_b_resp   ; 
    wire     [ID_BITS-1:0] tb_b_id     ; 
       // read address 
    wire                   tb_ar_valid; 
    wire                   tb_ar_ready; 
    wire  [TB_ADDR_WIDTH-1: 0] tb_ar_addr ; 
    wire     [ID_BITS-1:0] tb_ar_id   ; 
    wire    [LEN_BITS-1:0] tb_ar_len  ; 
    wire           [ 2: 0] tb_ar_size ; 
    wire           [ 1: 0] tb_ar_burst; 
    wire           [ 3: 0] tb_ar_cache; 
    wire           [ 1: 0] tb_ar_lock ; 
    wire           [ 2: 0] tb_ar_prot ; 
    wire           [ 3: 0] tb_ar_qos  ; 

       // read data
    wire                   tb_r_valid ; 
    wire                   tb_r_ready ; 
    wire   [TB_DATA_WIDTH-1:0] tb_r_data  ; 
    wire                   tb_r_last  ; 
    wire     [ID_BITS-1:0] tb_r_id    ; 
    wire           [ 1 :0] tb_r_resp  ; 

//***Module***
    AXI_PMU #(
		.C_S_AXI_DATA_WIDTH	(TB_DATA_WIDTH),
		.C_S_AXI_ADDR_WIDTH	(TB_ADDR_WIDTH)
    )
        dut_AXI_PMU(
        .S_AXI_ACLK_i     ( tb_clk_i                         ),
        .S_AXI_ARESETN_i  ( tb_rstn_i                        ),
        .S_AXI_AWADDR_i   ( tb_aw_addr      ),
        .S_AXI_AWVALID_i  ( tb_aw_valid     ),
        .S_AXI_AWREADY_o  ( tb_aw_ready     ),
        .S_AXI_WDATA_i    ( tb_w_data       ),
        .S_AXI_WSTRB_i    ( tb_w_strb       ),
        .S_AXI_WVALID_i   ( tb_w_valid      ),
        .S_AXI_WREADY_o   ( tb_w_ready      ),
        .S_AXI_BRESP_o    ( tb_b_resp       ),
        .S_AXI_BVALID_o   ( tb_b_valid      ),
        .S_AXI_BREADY_i   ( tb_b_ready      ),
        .S_AXI_ARADDR_i   ( tb_ar_addr      ),
        .S_AXI_ARVALID_i  ( tb_ar_valid     ),
        .S_AXI_ARREADY_o  ( tb_ar_ready     ),
        .S_AXI_RDATA_o    ( tb_r_data       ),
        .S_AXI_RRESP_o    ( tb_r_resp       ),
        .S_AXI_RVALID_o   ( tb_r_valid      ),
        .S_AXI_RREADY_i   ( tb_r_ready      ),
        .EV0_i            (tb_EV0_i),   
        .EV1_i            (tb_EV1_i),   
        .EV2_i            (tb_EV2_i),   
        .EV3_i            (tb_EV3_i),   
        .EV4_i            (tb_EV4_i),   
        .EV5_i            (tb_EV5_i),   
        .EV6_i            (tb_EV6_i),   
        .EV7_i            (tb_EV7_i),   
        .EV8_i            (tb_EV8_i),   
        .EV9_i            (tb_EV9_i),   
        .EV10_i            (tb_EV10_i),   
        .EV11_i            (tb_EV11_i),   
        .EV12_i            (tb_EV12_i),   
        .EV13_i            (tb_EV13_i),   
        .EV14_i            (tb_EV14_i),   
        .EV15_i            (tb_EV15_i),   
        .int_overflow_o (int_overflow_o),
        .int_quota_o(int_quota_o),
        .int_quota_c0_o(int_quota_c0_o),
        .int_quota_c1_o(int_quota_c1_o)
    );
//***Auxiliar modules for test***/
//Axi master to generate transactions

reg tb_run;
initial tb_run =0;
wire tb_done;
axi_test_master
   #(
      .ADRS_BITS (TB_ADDR_WIDTH),
      .DATA_BITS (TB_DATA_WIDTH),
      .LEN_BITS  (LEN_BITS) ,//The number of (burst) length bits
      .ID_BITS   (ID_BITS)// ,//The number of ID bits
                                 // Depth of the queues (FIFOs)
   ) // parameters
axi_test_master0 (

      .clk    (tb_clk_i),
      .reset_n(tb_rstn_i),
      .run    (tb_run),
      .done   (tb_done),
      
   // write address
      .awvalid(tb_aw_valid),
      .awready(tb_aw_ready),
      .awaddr (tb_aw_addr),
      .awlen  (tb_aw_len),
      .awsize (tb_aw_size),
      .awid   (tb_aw_id),
      .awburst(tb_aw_burst),
   
      .awcache(tb_aw_cache),
      .awlock (tb_aw_lock),
      .awprot (tb_aw_prot),
      .awqos  (tb_aw_qos),
                           
   // write data           
      .wvalid (tb_w_valid),
      .wready (tb_w_ready),
      .wdata  (tb_w_data),
      .wstrb  (tb_w_strb),
      .wlast  (tb_w_last),
      .wid    (tb_w_id),

   // write response    
      .bvalid (tb_b_valid),
      .bready (tb_b_ready),
      .bresp  (tb_b_resp),
      .rresp  (tb_r_resp),
      .bid    (tb_b_id),

   //........................
   
   // read address
      .arvalid(tb_ar_valid),
      .arready(tb_ar_ready),
      .araddr (tb_ar_addr),
      .arlen  (tb_ar_len),
      .arsize (tb_ar_size),
      .arid   (tb_ar_id),
      .arburst(tb_ar_burst),
   
      .arcache(tb_ar_cache),
      .arlock (tb_ar_lock),
      .arprot (tb_ar_prot),
      .arqos  (tb_ar_qos),
 
   // read data
      .rvalid (tb_r_valid),
      .rready (tb_r_ready),
      .rdata  (tb_r_data),
      .rlast  (tb_r_last),
      .rid    (tb_r_id)
 
       );
//***clk_gen***
    initial tb_clk_i = 1;
    always #CLK_HALF_PERIOD tb_clk_i = !tb_clk_i;

//***task automatic reset_dut***
    task automatic reset_dut;
        begin
            $display("***Reset");
            tb_rstn_i <= 1'b0; 
            #CLK_PERIOD;
            tb_rstn_i <= 1'b1;
            #CLK_PERIOD;
        end
    endtask 

//***task automatic init_sim***
//Initialize TB registers to a known state. Assumes good host
task automatic init_sim;
        begin
            if(VERBOSE)
            $display("*** init sim.");
            //*** TODO ***
            tb_clk_i <='{default:1};
            tb_rstn_i<='{default:0};
            tb_EV0_i <= '{default:0};
            tb_EV1_i <= '{default:0};
            tb_EV2_i <= '{default:0};
            tb_EV3_i <= '{default:0};
            tb_EV4_i <= '{default:0};
            tb_EV5_i <= '{default:0};
            tb_EV6_i <= '{default:0};
            tb_EV7_i <= '{default:0};
            tb_EV8_i <= '{default:0};
            tb_EV9_i <= '{default:0};
            tb_EV10_i <= '{default:0};
            tb_EV11_i <= '{default:0};
            tb_EV12_i <= '{default:0};
            tb_EV13_i <= '{default:0};
            tb_EV14_i <= '{default:0};
            tb_EV15_i <= '{default:0};
        end
    endtask

//***task automatic init_dump***
    task automatic init_dump;
        begin
            $dumpfile("AXI_PMU_test.vcd");
            $dumpvars(0,dut_AXI_PMU);
        end
    endtask 

//***task automatic test_sim***
    task automatic test_sim;
        begin
            $display("***Running ALL test");
            write_all_max;
            hw_reset_all;
            all_counters;
            $display("***Done ALL tests");
        end
    endtask 

//***task automatic write_all_max***
//This task checks that the wrapper of axi still handles the writtes propperly
//and the "selfreset" function of protected registers of MCCU are working
    task automatic write_all_max; 
        begin
            //other parameters
            //In last_addr.Substracting 1 to n_registers because we start on 0
            int unsigned tmp=0;
            tb_run=0;
            for (int w_addr=first_addr;w_addr <=last_addr;w_addr+=4) begin
                if(VERBOSE)
                $display("*** writting addres: %h with: 32'hffffffff",w_addr);
                axi_test_master0.q_wsync(
                        .address(w_addr),
                        .length(1),
                        .size(TB_DATA_WIDTH),
                        .id(0),
                        .burst(1),
                        .adelay_random(0),
                        .adelay(4),
                        .data(32'hffffffff),
                        .strobes(4'hf),
                        .last(1),
                        .wdelay_random(0),
                        .wdelay(5)
                );

            end
        if(VERBOSE) $display("*** addresses written");
        if(VERBOSE) $display("*** reading results ...");
        tb_run=1;
        //Let the master write the registers
        wait(tb_done);
        //check the registers of the counters after write into 32'hffffffff.
        //For this registers nothing shall change because are read only
        for (int i = base_counters; i<=last_counter; i=i+4) begin
            if (dut_AXI_PMU.inst_AXI_PMU.slv_reg[i>>2] != 32'b0) begin
                $error("FAIL write_all_max. Register %d is not 0", i>>2);
                tmp=1;
            end
        end
        //check the registers of PMU configuration after write into 
        //32'hffffffff. This registers must contain 32'hffffffff.
        for (int i = base_conf; i<=last_conf; i=i+4) begin
            if (dut_AXI_PMU.inst_AXI_PMU.slv_reg[i>>2] != 32'hffffffff) begin
                $error("FAIL write_all_max. Register %d has\
                        not been set to 32'hffffffff", i>>2);
                tmp=1;
            end
        end
        //check overflow registers. They must stay in 0 because no events have
        //been feeded in to the PMU and we started the with a hw reset.
        if(dut_AXI_PMU.inst_AXI_PMU.OVERFLOW)
        for (int i = base_overflow; i<=last_overflow; i=i+4) begin
            if (dut_AXI_PMU.inst_AXI_PMU.slv_reg[i>>2] != 32'b0) begin
                $error("FAIL write_all_max. Register %d is not 0", i>>2);
                tmp=1;
            end
        end
        //Check quota registers.  Both are  writable, so This registers must 
        //contain 32'hffffffff.
        if(dut_AXI_PMU.inst_AXI_PMU.QUOTA)
        for (int i = base_quota; i<=last_quota; i=i+4) begin
            if (dut_AXI_PMU.inst_AXI_PMU.slv_reg[i>>2] != 32'hffffffff) begin
                $error("FAIL write_all_max. Register %d has\
                        not been set to 32'hffffffff", i>>2);
                tmp=1;
            end
        end
        //check MCCU main configuration registers. Only the MSB of the main 
        //configuration register of the MCCU must be set to 1. The other bits
        //reset to 0 after one cycle if they have been written.
        if(dut_AXI_PMU.inst_AXI_PMU.MCCU)
        if (dut_AXI_PMU.inst_AXI_PMU.slv_reg[base_MCCU>>2] !=32'h80000000) begin
            $error("FAIL write_all_max. Main MCCU configuration register %d has\
                    not been set to 32'h80000000", base_MCCU>>2);
            tmp=1;
            end
        //check MCCU core Quota. This registers must be writable, so they must
        //contain 32'hffffffff
        if(dut_AXI_PMU.inst_AXI_PMU.MCCU)
        for (int i=first_MCCU_quota; i<=first_MCCU_quota+n_cores_MCCU; i=i+4)
        begin
            if (dut_AXI_PMU.inst_AXI_PMU.slv_reg[i>>2] != 32'hffffffff) begin 
                $error("FAIL write_all_max. Register %d has\
                        not been set to 32'hffffffff", i>>2);
                tmp=1;
            end
        end
        //check MCCU weights quota. This registers must be writable, so they
        //must contain 32'hffffffff
        if(dut_AXI_PMU.inst_AXI_PMU.MCCU)
        for (int i=first_MCCU_weights; i<=first_MCCU_weights+n_regs_MCCU_weights
            ; i=i+4) begin
            if (dut_AXI_PMU.inst_AXI_PMU.slv_reg[i>>2] != 32'hffffffff) begin
                $error("FAIL write_all_max. Register %d has\
                        not been set to 32'hffffffff", i>>2);
                tmp=1;
            end
        end
        //check MCCU interruption registers of consumed quota. This registers
        //can be written but will reset to the value generated by the MCCU in
        //the next cycle. As we start with a reset and no events have been
        //risen the output must be 0.
        if(dut_AXI_PMU.inst_AXI_PMU.MCCU)
        for (int i=first_MCCU_out_quota; i<=first_MCCU_weights+n_cores_MCCU
            ; i=i+4) begin
            if (dut_AXI_PMU.inst_AXI_PMU.slv_reg[i>>2] != 32'b0) begin
                $error("FAIL write_all_max. Register %d has\
                        not been set to 32'h00000000", i>>2);
                tmp=1;
            end
        end
        read_all; 
        if(tmp==0)
        `START_GREEN_PRINT
                $display("PASS write_all_max.");
        `END_COLOR_PRINT
        end
    endtask
//***task automatic read_all***
//Read all registers and print results
    task automatic read_all;
        begin
            int value;
            for (int r_addr=first_addr;r_addr <=last_addr ;r_addr+=4) begin
                axi_test_master0.q_radrs(
                        .address(r_addr),
                        .length(1),
                        .size(TB_DATA_WIDTH),
                        .id(0),
                        .burst(1),
                        .delay_random(0),
                        .delay(4)
                );
                tb_run = 1;
                wait(tb_done);
                value = tb_r_data;  
                if(VERBOSE) $display("*** readed addres: %h with value: %h",r_addr,value);
            end
        end
    endtask
//***task automatic hw_reset_all***
//Read all registers after a hw_reset and check expected values
//No events enabled
    task automatic hw_reset_all;
        begin
            int value, tmp=0;
            reset_dut;
            for (int r_addr=first_addr;r_addr <=last_addr ;r_addr+=4) begin
                axi_test_master0.q_radrs(
                        .address(r_addr),
                        .length(1),
                        .size(TB_DATA_WIDTH),
                        .id(0),
                        .burst(1),
                        .delay_random(0),
                        .delay(4)
                );
                tb_run = 1;
                wait(tb_done);
                value = tb_r_data;
                if (value!=32'b0) begin
                    `START_RED_PRINT
                    $error("FAIL reset_all. Register %d has\
                        not been set to 32'h00000000", r_addr>2);
                    `END_COLOR_PRINT
                    tmp=1;
                    end
            end
        if(tmp==0)
        `START_GREEN_PRINT
                $display("PASS hw_reset_all.");
        `END_COLOR_PRINT
        end
    endtask
//***task automatic all_counters***
//Enable counters sequentially. Count up, reset, rise overflow & check
//interrupt.
    task automatic all_counters;
        begin
            int value=0, tmp=0, up2='h1f;
            //set configuration through AXI-LITE commands
            int w_addr = main_conf;
            int set_reg = 32'h1; 
            if(VERBOSE)
            $display("*** writting addres: %h with: %h",w_addr,set_reg);
            axi_test_master0.q_wsync(
                    .address(w_addr),
                    .length(1),
                    .size(TB_DATA_WIDTH),
                    .id(0),
                    .burst(1),
                    .adelay_random(0),
                    .adelay(4),
                    .data(set_reg),
                    .strobes(4'hf),
                    .last(1),
                    .wdelay_random(0),
                    .wdelay(5)
            );
            //Execute configuration  commands
                tb_run = 1;
                wait(tb_done);
            //Trigger events
            enable_all_events;
            //Run
            while(value<=up2) begin
                #CLK_PERIOD;
                value++;
            end
            //Disable events
            disable_all_events; 
            //Read results
            for (int r_addr=base_counters;r_addr <=last_counter;r_addr+=4) begin
                axi_test_master0.q_radrs(
                        .address(r_addr),
                        .length(1),
                        .size(TB_DATA_WIDTH),
                        .id(0),
                        .burst(1),
                        .delay_random(0),
                        .delay(4)
                );
                value = tb_r_data;
                if (up2!=dut_AXI_PMU.inst_AXI_PMU.slv_reg[r_addr>>2]) begin
                    $error("FAIL all_counters. Register %d has captured %h \
                    events instead of expected %h", r_addr>2,dut_AXI_PMU.inst_AXI_PMU.slv_reg[r_addr>>2], up2);
                    tmp=1;
                end
            end
            //Tests Overflow by setting counter near overflow
            for (int r_addr=base_counters;r_addr <=last_counter;r_addr+=4) begin
                dut_AXI_PMU.inst_AXI_PMU.slv_reg[r_addr>>2] ='hffffffff;
            end
            //Trigger events
            enable_all_events;
            #CLK_PERIOD;
            #CLK_PERIOD;
            //Read Overflow registers
            //TODO: This is only valid up to 16 input signals
            axi_test_master0.q_radrs(
                    .address(base_overflow),
                    .length(1),
                    .size(TB_DATA_WIDTH),
                    .id(0),
                    .burst(1),
                    .delay_random(0),
                    .delay(4)
            );
            value = tb_r_data;
            up2 ='hffff;
            if (dut_AXI_PMU.inst_AXI_PMU.slv_reg[base_overflow>>2]!=up2) begin
                $error("FAIL all_counters. Overflow register %d has captured %h \
                    interrupts instead of expected %h", base_overflow>2
                    ,dut_AXI_PMU.inst_AXI_PMU.slv_reg[base_overflow>>2], up2);
                tmp=1;
            end
            if(int_overflow_o != 1'b1)
                $error("Overflow Interrupt has not been risen");
        if(tmp==0)
        `START_GREEN_PRINT
            $display("PASS overflow_counters.");
            $display("PASS all_counters.");
        `END_COLOR_PRINT
        end
        
    endtask enable_all_events
        begin
        //Trigger events
        tb_EV0_i=1;
        tb_EV1_i=1;
        tb_EV2_i=1;
        tb_EV3_i=1;
        tb_EV4_i=1;
        tb_EV5_i=1;
        tb_EV6_i=1;
        tb_EV7_i=1;
        tb_EV8_i=1;
        tb_EV9_i=1;
        tb_EV10_i=1;
        tb_EV11_i=1;
        tb_EV12_i=1;
        tb_EV13_i=1;
        tb_EV14_i=1;
        tb_EV15_i=1;
        end
    endtask 

    task disable_all_events 
        begin
            //Trigger events
            tb_EV0_i=0;
            tb_EV1_i=0;
            tb_EV2_i=0;
            tb_EV3_i=0;
            tb_EV4_i=0;
            tb_EV5_i=0;
            tb_EV6_i=0;
            tb_EV7_i=0;
            tb_EV8_i=0;
            tb_EV9_i=0;
            tb_EV10_i=0;
            tb_EV11_i=0;
            tb_EV12_i=0;
            tb_EV13_i=0;
            tb_EV14_i=0;
            tb_EV15_i=0;
        end
    endtask


//***task automatic Quota_monitor***
//Mask some signals, count up. Check masked signals do not count up.
//Set a limit, wait until the interruption is enabled.
    task automatic quota_monitor
        begin
        //reset the PMU
        reset_dut;
        //Set the mask
            //set quota mask PMU through AXI-LITE commands, Only selected
            //events will substract quota.
            int w_addr = first_quota_mask;
            int set_reg = 32'b1010; 
            if(VERBOSE)
            $display("*** writting addres: %h with: %h",w_addr,set_reg);
            axi_test_master0.q_wsync(
                    .address(w_addr),
                    .length(1),
                    .size(TB_DATA_WIDTH),
                    .id(0),
                    .burst(1),
                    .adelay_random(0),
                    .adelay(4),
                    .data(set_reg),
                    .strobes(4'hf),
                    .last(1),
                    .wdelay_random(0),
                    .wdelay(5)
            );
            //set main configuration  register PMU through AXI-LITE commands
            int w_addr = main_conf;
            int set_reg = 32'h1; 
            if(VERBOSE)
            $display("*** writting addres: %h with: %h",w_addr,set_reg);
            axi_test_master0.q_wsync(
                    .address(w_addr),
                    .length(1),
                    .size(TB_DATA_WIDTH),
                    .id(0),
                    .burst(1),
                    .adelay_random(0),
                    .adelay(4),
                    .data(set_reg),
                    .strobes(4'hf),
                    .last(1),
                    .wdelay_random(0),
                    .wdelay(5)
            );
            //Execute configuration  commands
            tb_run = 1;
            wait(tb_done);
        //Rise several events
        enable_all_events;        
        //check reduction in quota
        //Set limit
        //trigger more events
        //Expect interrupt
        end
    endtask

//***init_sim***
    initial begin
        init_sim();
        init_dump();
        reset_dut();
        test_sim();
    end

endmodule
`default_nettype wire

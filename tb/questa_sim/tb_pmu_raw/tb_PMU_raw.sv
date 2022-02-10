/* -----------------------------------------------
* Project Name   : MCCU research 
* File           : tb_pmu_raw.sv_
* Organization   : Barcelona Supercomputing Center
* Author(s)      : Guillem cabo 
* Email(s)       : guillem.cabo@bsc.es
* References     : 
* -----------------------------------------------
* Revision History
*  Revision   | Author    | Commit | Description
*  0.0        | G.cabo    |        | Initial commit
* -----------------------------------------------
*/

//-----------------------------------------------------
// Function   : Debug integration of MCCU
// Description: Designed to be used with QuestaSim.

`timescale 1 ns / 1 ns
`default_nettype none
`include "colors.vh"
//***Headers***
//***Test bench***
module tb_PMU_raw();
//***Parameters***
    parameter CLK_PERIOD            = 2;
    parameter CLK_HALF_PERIOD       = CLK_PERIOD / 2;
//***DUT parameters***    
    parameter TB_REG_WIDTH          = 32 ;
    parameter TB_N_COUNTERS         = 24 ;
    parameter TB_N_SOC_EV           = 128;    
    parameter TB_MCCU_N_CORES       = 6  ;
    parameter TB_N_CONF_REGS        = 1  ;    
    parameter TB_MCCU_WEIGHTS_WIDTH = 8  ;
    parameter TB_MCCU_N_EVENTS      = 2  ;
    parameter FT= 0;

        //------------- Internal Parameters 		
        // *** Active functions and global configuration
        //---- Overflow
    localparam integer OVERFLOW	= 1; //Yes/No
    //---- Quota
    localparam integer QUOTA	= 1; //Yes/No
    //---- MCCU - Maximum-contention Control Unit mode
    localparam integer MCCU	    = 1; //Yes/No
    //---- RDC - Request Duration Counters
    localparam integer RDC	    = 1; //Yes/No
    //---- Crossbar
    localparam integer CROSSBAR	= 1; //Yes/No

     //---- MCCU registers and parameters
        // General parameters feature
    localparam BASE_CFG       = 0;
       // Main configuration register for the MCCU 
    localparam N_MCCU_CFG     = 1;		
    // Quota limit assgined to each core
    localparam N_MCCU_LIMITS  = TB_MCCU_N_CORES;
    // Currently available Quota for each core
    localparam N_MCCU_QUOTA   = TB_MCCU_N_CORES;
    // Weights for each one of the available events
    localparam N_MCCU_WEIGHTS = (((TB_MCCU_N_CORES*TB_MCCU_N_EVENTS*TB_MCCU_WEIGHTS_WIDTH)-1)/TB_REG_WIDTH+1);
    //--- MCCU registers  
    localparam N_MCCU_REGS    = (N_MCCU_CFG + N_MCCU_LIMITS + N_MCCU_QUOTA + N_MCCU_WEIGHTS) * MCCU;
    
    //---- RDC registers and parameters. Shared with MCCU 
        // General parameters feature
    localparam N_RDC_WEIGHTS   = 0; 	
      // Interruption vector 
    localparam N_RDC_VECT_REGS =  ((TB_MCCU_N_CORES*TB_MCCU_N_EVENTS-1)/TB_REG_WIDTH+1);
    // Watermark for each one of the available events
    localparam N_RDC_WATERMARK = (((TB_MCCU_N_CORES*TB_MCCU_N_EVENTS*TB_MCCU_WEIGHTS_WIDTH)-1)/TB_REG_WIDTH+1);
    //--- RDC registers 
    localparam N_RDC_REGS      = (N_RDC_WEIGHTS + N_RDC_VECT_REGS+N_RDC_WATERMARK) * RDC;
    //---- OVERFLOW registers
    localparam N_OVERFLOW_REGS = 2*((TB_N_COUNTERS-1)/TB_REG_WIDTH+1) * OVERFLOW;
    //---- QUOTA registers
    localparam N_QUOTA_REGS    = 2*((TB_N_COUNTERS-1)/TB_REG_WIDTH+1) * QUOTA;
    //---- CROSSBAR registers
    localparam N_CROSSBAR_CFG  = ((TB_N_COUNTERS*$clog2(TB_N_SOC_EV)-1)/TB_REG_WIDTH+1) * CROSSBAR;
    localparam N_CROSSBAR_REGS = N_CROSSBAR_CFG;
    localparam CROSSBAR_CFG_BITS = $clog2(TB_N_SOC_EV);
   
    localparam END_MCCU_WEIGHTS   =  BASE_CFG + TB_N_CONF_REGS + TB_N_COUNTERS + N_OVERFLOW_REGS + N_QUOTA_REGS + N_MCCU_CFG + N_MCCU_LIMITS  + TB_MCCU_N_CORES -1 +  N_MCCU_WEIGHTS;      
    localparam BASE_RDC_VECT      = END_MCCU_WEIGHTS+1;
    localparam BASE_RDC_WATERMARK =  BASE_RDC_VECT + N_RDC_VECT_REGS; 
    localparam BASE_CROSSBAR      = BASE_RDC_WATERMARK + N_RDC_WATERMARK;

  //---- Total of registers used
    localparam integer TB_TOTAL_NREGS = TB_N_COUNTERS + TB_N_CONF_REGS + N_MCCU_REGS + N_RDC_REGS + N_OVERFLOW_REGS + N_QUOTA_REGS + N_CROSSBAR_REGS;	
  
    
//***Signals***
    reg                         tb_clk_i                               ;
    reg                         tb_rstn_i                              ;
    reg   [TB_N_SOC_EV-1:0]     tb_events_i                            ;
    logic [TB_REG_WIDTH-1:0]    tb_regs_i          [0:TB_TOTAL_NREGS-1];
    wire  [TB_REG_WIDTH-1:0]    tb_regs_o          [0:TB_TOTAL_NREGS-1];
    reg                         tb_wrapper_we_i                        ;
    wire                        tb_intr_overflow_o                     ;
    wire                        tb_intr_quota_o                        ;
    wire  [TB_MCCU_N_CORES-1:0] tb_intr_MCCU_o                         ;
    wire                        tb_intr_RDC_o                          ;

//store name of test for easier debug of waveform
reg [64*8:0] tb_test_name;
reg          tb_fail = 0 ;
//***Module***
    PMU_raw #(         
        .REG_WIDTH          (TB_REG_WIDTH         ),
        .N_COUNTERS         (TB_N_COUNTERS        ),
        .N_SOC_EV           (TB_N_SOC_EV          ),
        .MCCU_N_CORES       (TB_MCCU_N_CORES      ),
        .N_CONF_REGS        (TB_N_CONF_REGS       ),
        .MCCU_WEIGHTS_WIDTH (TB_MCCU_WEIGHTS_WIDTH),
        .MCCU_N_EVENTS      (TB_MCCU_N_EVENTS     ),
        .FT                 (FT                   )
	)dut_PMU_raw (
		.clk_i           (tb_clk_i          ),
		.rstn_i          (tb_rstn_i         ),
        .regs_i          (tb_regs_i         ),
        .regs_o          (tb_regs_o         ),
        .wrapper_we_i    (tb_wrapper_we_i   ),
        .events_i        (tb_events_i       ),
        .intr_overflow_o (tb_intr_overflow_o),
        .intr_quota_o    (tb_intr_quota_o   ),
        .intr_MCCU_o     (tb_intr_MCCU_o    ),
        .intr_FT1_o      (                  ),
        .intr_FT2_o      (                  ),
        .intr_RDC_o      (tb_intr_RDC_o     )
	);

//***clk_gen***
    initial tb_clk_i = 1;
    always #CLK_HALF_PERIOD tb_clk_i = !tb_clk_i;

//***task automatic reset_dut***
    task automatic reset_dut;
        begin
            $display("*** Toggle reset.");
            tb_rstn_i <= 1'b0; 
            #CLK_PERIOD;
            tb_rstn_i <= 1'b1;
            #CLK_PERIOD;
            $display("Done");
        end
    endtask 

//***task automatic init_sim***
//Initialize TB registers to a known state. 
task automatic init_sim;
        begin
            $display("*** init sim.");
            tb_clk_i        <='{default:1};
            tb_rstn_i       <='{default:0};
            tb_events_i     <='{default:0};
            tb_regs_i       <='{default:0};
            tb_wrapper_we_i <='{default:0};
            $display("Done");
        end
    endtask

//***task automatic init_dump***
    task automatic init_dump;
        begin
            $dumpfile("MCCU_test.vcd");
            $dumpvars(0,dut_PMU_raw);
        end
    endtask 

//***task automatic write_reg***
task automatic write_reg (input int register, value);
    begin
        tb_regs_i[register] = value;
        tb_wrapper_we_i     = 1;
        #CLK_PERIOD;
        tb_wrapper_we_i     = 0;
    end
endtask

//***task automatic test_MCCU_1
task automatic test_MCCU_1;
    begin
        tb_test_name="test_MCCU_1";
        write_reg(0,32'h00000012);
        write_reg(29,32'b10);
        write_reg(29,32'b10);
        write_reg(0,32'h40000001);
        write_reg(38,32'h01020304);
        write_reg(39,32'h05060708);
        write_reg(30,32'hffffffff);
        write_reg(31,32'haaaaaaaa);
        write_reg(32,32'hbbbbbbbb);
        write_reg(33,32'hcccccccc);
        write_reg(29,32'b0111100);
        write_reg(29,32'b0000001);
        #CLK_PERIOD;
        #CLK_PERIOD;
        #CLK_PERIOD;
        #CLK_PERIOD;
        #CLK_PERIOD;
        #CLK_PERIOD;
        #CLK_PERIOD;
    end
endtask
//***task automatic route_ito***
    // This taks takes two parameters. First parameter
    // is the input event. The second parameter is the 
    // selected output. The function enables the input
    // sets the configuration register and checks if
    // the signal reaches the output.

logic [TB_N_SOC_EV-1:0]                 unpack_crossbar_cfg [0:TB_N_COUNTERS];
logic [N_CROSSBAR_CFG*TB_REG_WIDTH-1:0] concat_cfg_crossbar                  ;
//Map unpacked configuration registers to concatenation
integer i;
always_comb begin
    for (i=0; i < TB_N_COUNTERS; i++) begin
       concat_cfg_crossbar[CROSSBAR_CFG_BITS*i+:CROSSBAR_CFG_BITS] = unpack_crossbar_cfg[i];
    end
end
//Map concatenation to configuration registers
integer j;
always_comb begin
    for (j=0; j < N_CROSSBAR_CFG; j++) begin
       tb_regs_i[BASE_CROSSBAR+j]=concat_cfg_crossbar[j*TB_REG_WIDTH+:TB_REG_WIDTH];
    end
end
// Now we can drive unpack_crossbar_cfg with route_ito and get the values in tb_regs_i without
    //any conversion
    task automatic route_ito (input int in, out, output int tb_fail);
        begin
            tb_test_name = "route_ito";
            //set all other signals to 0
            tb_events_i  <= '{default:0}; 
            //enable signal that we want to route
            #CLK_PERIOD;
            tb_events_i[in] = 1;
            //clear previous configuration
            unpack_crossbar_cfg <= '{default:0};
            #CLK_PERIOD;
            //set new configuration
            unpack_crossbar_cfg[out] <= in;  
            #CLK_PERIOD;
            #CLK_PERIOD;
            //check if the output signal is enabled
            if(dut_PMU_raw.unpacked_cbo_int[out]!=1) begin
                tb_fail = 1; 
                `START_RED_PRINT
                $error("FAIL.%d routed to %d. Expected output value is 1", in, out); 
                `END_COLOR_PRINT
            end

        end
    endtask 
//***test all routing combinations crossbar
    task automatic test_crossbar;
        begin
            integer rval;
            integer test_fail;
            // try all the input and output combinations
            integer i; //inputs iterator
            integer j; // output iterator
            for(i=0;i<TB_N_SOC_EV;i++) begin
                for(j=0;j<TB_N_COUNTERS;j++) begin
                    route_ito(i,j,rval);
                    test_fail = rval + test_fail;
                end
            end
            if (test_fail == 0) begin
                `START_GREEN_PRINT
                $error("PASS routing tests"); 
                `END_COLOR_PRINT
            end
        end
    endtask 


//***task automatic test_sim***
    task automatic test_sim;
        begin
            int unsigned temp=1;
            $display("*** test_sim.");
            tb_test_name="test_sim";
            //**test***
            test_MCCU_1();
            //check results
            if(temp!=1) begin
                tb_fail = 1; 
                $error("FAIL test_sim. Expected interruption high");
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
            $display("Done");
        end
    endtask 

//***init_sim***
    initial begin
        integer retv;
        init_sim();
        init_dump();
        reset_dut();
        test_sim();
        //Disable PMU and selftest modes
        write_reg(0,32'h00000000);
        test_crossbar;
        $display("FT = %d",FT);
        $finish;
    end

endmodule
`default_nettype wire

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
    parameter CLK_PERIOD      = 2;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
//***DUT parameters***    
    parameter TB_DATA_WIDTH = 32;
    parameter TB_N_COUNTERS = 24;
    parameter TB_N_CFG = 1;
    parameter TB_N_CORES= 4;
    //WARNIGN: if N_counters or cores change this value needs to change
    parameter TB_TOTAL_NREGS= 43;
    
//***Signals***
    reg     tb_clk_i ;
    reg     tb_rstn_i ;
    reg  [TB_N_COUNTERS-1:0] tb_events_i;
    reg  [TB_DATA_WIDTH-1:0] tb_regs_i [0:TB_TOTAL_NREGS-1];
    wire  [TB_DATA_WIDTH-1:0] tb_regs_o [0:TB_TOTAL_NREGS-1];
    reg tb_wrapper_we_i;
    wire tb_intr_overflow_o;
    wire tb_intr_quota_o;
    wire [TB_N_CORES-1:0] tb_intr_MCCU_o;
    wire tb_intr_RDC_o;

//store name of test for easier debug of waveform
reg[64*8:0] tb_test_name;
reg tb_fail = 0;
//***Module***
    PMU_raw #(
		.REG_WIDTH(TB_DATA_WIDTH),
		.N_COUNTERS(TB_N_COUNTERS),
		.N_CONF_REGS(TB_N_CFG)
	)dut_PMU_raw (
		.clk_i(tb_clk_i),
		.rstn_i(tb_rstn_i),
        .regs_i(tb_regs_i),
        .regs_o(tb_regs_o),
        .wrapper_we_i(tb_wrapper_we_i),
        .events_i(tb_events_i),
        .intr_overflow_o(tb_intr_overflow_o),
        .intr_quota_o(tb_intr_quota_o),
        .intr_MCCU_o(tb_intr_MCCU_o),
        .intr_RDC_o(tb_intr_RDC_o)
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
            tb_clk_i <='{default:1};
            tb_rstn_i<='{default:0};
            tb_events_i <='{default:0};
            tb_regs_i <='{default:0};
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
        tb_wrapper_we_i = 1;
        #CLK_PERIOD;
        tb_wrapper_we_i = 0;
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
        init_sim();
        init_dump();
        reset_dut();
        test_sim();
        $finish;
    end

endmodule
`default_nettype wire

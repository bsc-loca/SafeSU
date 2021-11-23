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
module tb_pmu_ahb();
//***Parameters***
    parameter CLK_PERIOD      = 2;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
//***DUT parameters***    
    parameter TB_DATA_WIDTH = 32;
    parameter TB_N_COUNTERS = 24;
	parameter TB_N_SOC_EV	= 32;
    parameter TB_N_CFG = 1;
    parameter TB_N_CORES= 4;
    //WARNIGN: if N_counters or cores change this value needs to change
    parameter TB_TOTAL_NREGS= 47;
    parameter FT = 0;     
//***Signals***
    reg clk_i ;
    reg rstn_i ;
    reg [TB_N_SOC_EV-1:0] events_i;
    //AHB signals
    reg hsel_i;
    reg hwrite_i;
    reg [TB_DATA_WIDTH-1:0] haddr_i;
    reg [TB_DATA_WIDTH-1:0] hwdata_i;
    reg [1:0] htrans_i;
    wire [1:0] hresp_o;
    wire [TB_DATA_WIDTH-1:0] hrdata_o;
    wire  hreadyo_o;

//store name of test for easier debug of waveform
reg[64*8:0] tb_test_name;
reg tb_fail = 0;
//***Module***
	pmu_ahb #
	(
        .haddr(32'h80100000),                                                  
        .hmask(32'hfff),                                           
        .REG_WIDTH(32),
        .N_REGS(TB_TOTAL_NREGS), 
        .MCCU_N_CORES(4),
	    .N_SOC_EV (TB_N_SOC_EV),
        .FT(FT)
	)
    dut_pmu_ahb 
	(
        .rstn_i(rstn_i),
        .clk_i(clk_i),
        .hsel_i(hsel_i),                               
        .hreadyi_i(1'b1),
        .haddr_i(haddr_i),
        .hwrite_i(hwrite_i),
        .htrans_i(htrans_i),
        .hsize_i(3'b0),
        .hburst_i(3'b0),
        .hwdata_i(hwdata_i),
        .hprot_i(4'b0),
        .hmastlock_i(1'b0),
        .hreadyo_o(hreadyo_o),
        .hresp_o(),
        .hrdata_o(hrdata_o),
        .events_i(events_i),
        .intr_overflow_o(),
        .intr_quota_o(),
        .intr_MCCU_o(),
        .intr_RDC_o(),
        .intr_FT1_o(),
        .intr_FT2_o()
    );

//***clk_gen***
    initial clk_i = 1;
    always #CLK_HALF_PERIOD clk_i = !clk_i;

//***task automatic reset_dut***
    task automatic reset_dut;
        begin
            $display("*** Toggle reset.");
            rstn_i <= 1'b0; 
            hsel_i = 0;
            htrans_i = 2'b00;
            #CLK_PERIOD;
            #CLK_PERIOD;
            rstn_i <= 1'b1;
            #CLK_PERIOD;
            $display("Done");
        end
    endtask 

//***task automatic init_sim***
//Initialize TB registers to a known state. 
task automatic init_sim;
        begin
            $display("*** init sim.");
            clk_i <='{default:1};
            rstn_i<='{default:0};
            events_i <='{default:0};
            $display("Done");
        end
    endtask

//***task automatic init_dump***
    task automatic init_dump;
        begin
            $dumpfile("MCCU_test.vcd");
            $dumpvars(0,dut_pmu_ahb);
        end
    endtask 

//*** Single word sequential ahb write request
    task automatic sws_ahb_w (input int addr, data, output int rval);
        begin
            int rval;
            integer test_fail;
            localparam TRANS_SEQUENTIAL = 2'b11;
            // wait for ready
            while (!hreadyo_o) begin
            #CLK_PERIOD;
            end
            //Once ready is available
            hsel_i = 1;
            hwrite_i = 1;
            htrans_i = TRANS_SEQUENTIAL;
            haddr_i = addr;
            hwdata_i = data;
            #CLK_PERIOD;
            //wait for acknowledge and  finish request
            while (hresp_o != 2'b01) begin
            #CLK_PERIOD;
            end
            hsel_i = 0;
            hwrite_i = 0;
            htrans_i = TRANS_SEQUENTIAL;
            haddr_i = addr;
            hwdata_i = 32'hc7a9c7a9;
            //For now i don't check the results
            rval = 1;
        end
    endtask 
//Run "a" cycles, random input events
task automatic rand_run(input longint a);
        begin
            integer i;
            $display("*** rand srun %0d.",a);
            tb_test_name="rand_run";
            for(i=0;i<a;i++) begin
            #CLK_PERIOD;
            events_i <= $random();
            end
            $display("Done");
        end
    endtask


//***task automatic test_sim***
    task automatic test_sim;
        begin
            int tmp =1;
            $display("*** test_sim");
            // Simple writes tests
            sws_ahb_w(32'h8010000,32'h2,tmp);
            sws_ahb_w(32'h8010000,32'h1,tmp);
            sws_ahb_w(32'h801000ac,32'hcafecafe,tmp);
            sws_ahb_w(32'h801000ac,$random(),tmp);
            sws_ahb_w(32'h801000b0,$random(),tmp);
            sws_ahb_w(32'h801000b4,$random(),tmp);
            sws_ahb_w(32'h801000b8,$random(),tmp);
            rand_run(50);
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
        $display("FT = %d",FT);
        $finish;
    end

endmodule
`default_nettype wire

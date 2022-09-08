//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : TB for single event transient error detector for comb. logic. 
// Description: This module takes a signal coming from a combinational block 
//              and registers the signal at two different points of the clock cycle.
//              To achive that two clocks are needed, one is the regular system clock
//              , the other has to be delayed by  a given amount based on the type
//              of faults and the clock period of the implementation. 
//              Designed to be used with QuestaSim.
//
// Coder      : G.Cabo
// References : Fault-Tolerance Techniques for SRAM-Based FPGAs - ISBN 978-0-387-31069-5 

`timescale 1 ns / 1 ns
`default_nettype none
`include "colors.vh"
//***Headers***
//***Test bench***
module tb_com_tr();
//***Parameters***
    parameter CLK_PERIOD      = 8;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
    parameter CLK_QUARTER_PERIOD = CLK_HALF_PERIOD/ 2;
//***DUT parameters***    
    parameter TB_IN_WIDTH = 32;
    
//***Signals***
    reg     tb_clk_i ;
    reg     tb_dclk_i ;
    reg     tb_rstn_i ;
    reg     [TB_IN_WIDTH-1:0] tb_signal_i;
    reg     tb_error_o;

//store name of test for easier debug of waveform
reg[64*8:0] tb_test_name;
reg tb_fail = 0;
//***Module***
    com_tr #(
		.IN_WIDTH(TB_IN_WIDTH)
	)dut_com_tr (
		.clk_i(tb_clk_i),
		.dclk_i(tb_dclk_i),
		.rstn_i(tb_rstn_i),
		.signal_i(tb_signal_i),
		.error_o(tb_error_o)
	);

//***clk_gen***
    initial tb_clk_i = 1;
    initial tb_dclk_i = 1;
    always #CLK_HALF_PERIOD tb_dclk_i = !tb_dclk_i;
    always @(posedge tb_dclk_i, negedge tb_dclk_i) begin
        #CLK_QUARTER_PERIOD;
        tb_clk_i= !tb_clk_i;
    end
//***task automatic reset_dut***
    task automatic reset_dut;
        begin
            $display("*** Toggle reset.");
            tb_test_name = "reset_dut";
            tb_rstn_i <= 1'b0; 
            #CLK_PERIOD;
            tb_rstn_i <= 1'b1;
            #CLK_PERIOD;
            $display("Done");
            tb_test_name = "";
        end
    endtask 

//***task automatic init_sim***
//Initialize TB registers to a known state. 
task automatic init_sim;
        begin
            $display("*** init sim.");
            tb_test_name = "init_sim";
            $display("Done");
            tb_test_name = "";
        end
    endtask

//***task automatic init_dump***
    task automatic init_dump;
        begin
            $dumpfile("test.vcd");
            $dumpvars(0,dut_com_tr);
        end
    endtask 

//***task automatic test_sim***
    task automatic test_sim;
        begin
            int unsigned temp=1;
            $display("*** test_sim.");
            tb_test_name="test_sim";
            //Sync with main clock
            #CLK_HALF_PERIOD;
            #CLK_QUARTER_PERIOD;
            //**test***
            test_no_seu(100000,temp);
            test_meu(100000,temp);
            //check results
            if(temp!=1) begin
                tb_fail = 1; 
                $error("FAIL test_sim.");
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
            $display("Done");
            tb_test_name="";
        end
    endtask 
    
//***task automatic test_no_seu***
//  Random input events are generated, but no
//  single event upsets are forced.
//  Returns 0 if test fails and 1 if test passes
    task automatic test_no_seu(input int n_tries, output int rval);
        begin
            int tmp=0;
            $display("*** test_no_seu");
            tb_test_name="test_no_seu";
            //**test***
            for(int i=0;i<n_tries;i++) begin
                tb_signal_i = $urandom();
                #CLK_PERIOD;
                //check results
                if(tb_error_o!=0) begin
                    tmp=1;
                end
            end
            //check results
            if(tmp!=0) begin
                $error("FAIL test_no_seu. SEU detected but no SEU has been generated");
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
                rval=0;
            end
            $display("Done");
            tb_test_name="";
            rval=1;
        end
    endtask 

//***task automatic test_meu***
//  Random input events are generated, along
//  single or multiple event upsets at the rising edge of main clock.
//  Returns 0 if test fails and 1 if test passes
    task automatic test_meu(input int n_tries, output int rval);
        begin
            int valid_value;
            int upset_value;
            int tmp=0;
            $display("*** test_meu");
            tb_test_name="test_meu";
            //**test***
            for(int i=0;i<n_tries;i++) begin
                valid_value = $urandom();
                upset_value = $urandom();
                //Ensure that the upset actually changes the value
                while(upset_value == valid_value) begin
                    upset_value = $urandom();
                end
                //set the invalid value over the rising edge of main clock
                tb_signal_i =upset_value;
                #CLK_QUARTER_PERIOD
                //after a fiven period smaller than  the delay of dclock the
                    //valid value is set to the inputs
                tb_signal_i =valid_value;
                #CLK_QUARTER_PERIOD
                #CLK_QUARTER_PERIOD
                #CLK_QUARTER_PERIOD
                //Errors are registered and take one extra cycle to be signaled from output register
                //check results
                #CLK_PERIOD;
                if(tb_error_o!=1) begin
                    tmp=1;
                end
            end
            //check results
            if(tmp!=0) begin
                $error("FAIL test_meu.Some SEU have not detected");
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
                rval=0;
            end
            $display("Done");
            tb_test_name="";
            rval=1;
        end
    endtask 
    initial begin
        integer retv;
        tb_rstn_i<='{default:0};
        tb_signal_i <='{default:0};
        init_sim();
        init_dump();
        reset_dut();
        test_sim();
        $finish;
    end

endmodule
`default_nettype wire

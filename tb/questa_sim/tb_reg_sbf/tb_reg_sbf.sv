//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : TB for Single bit-flip error detector circuit.
// Description: This module takes a signals coming from the input of a register,
//              computes an even parity bit at the input and registers its value. The output
//              of the monitored register is used afterwards to compute again the parity bit.
//              If the parity bit at the output is different to the previous parity bit and
//              error is signaled.
//
//              Number of ones for data + parity bit shall be even.
//
//              Error signal is only active while the bit-flip is present in the circuit aka
//              the error signal is NOT holded until it is handled.
//
// Coder      : G.Cabo
// References : Fault-Tolerance Techniques for SRAM-Based FPGAs - ISBN 978-0-387-31069-5 

`timescale 1 ns / 1 ns
`default_nettype none
`include "colors.vh"
//***Headers***
//***Test bench***
module tb_reg_sbf();
//***Parameters***
    parameter CLK_PERIOD      = 8;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
    parameter CLK_QUARTER_PERIOD = CLK_HALF_PERIOD/ 2;
    parameter TB_IN_WIDTH = 32;
//***DUT parameters***    
    reg     tb_clk_i;
    reg     tb_rstn_i;
    reg     tb_error_o;
    logic [TB_IN_WIDTH-1:0] prot_reg;
    logic [TB_IN_WIDTH-1:0] prot_reg_d;
    logic [TB_IN_WIDTH-1:0] prot_reg_q;
    var integer valid_value;
    var integer upset_value;

//store name of test for easier debug of waveform
reg[64*8:0] tb_test_name;
reg tb_fail = 0;
//***Module***
    reg_sbf #(
		.IN_WIDTH(TB_IN_WIDTH)
	)dut_reg_sbf (
        .clk_i(tb_clk_i),
		.rstn_i(tb_rstn_i),
		.regi_i(prot_reg_d),
		.rego_i(prot_reg_q),
		.error_o(tb_error_o)
	);
// Instance of protected register and output wires

always_ff @(posedge tb_clk_i) begin
    if(!tb_rstn_i) begin
        prot_reg <= '{default:'0};
    end else begin
        prot_reg <= prot_reg_d;
    end
end

assign prot_reg_q = prot_reg; 

//***clk_gen***
    initial tb_clk_i = 1;
    always #CLK_HALF_PERIOD tb_clk_i = !tb_clk_i;
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
            $dumpvars(0,dut_reg_sbf);
        end
    endtask 

//***task automatic test_sim***
    task automatic test_sim;
        begin
            int unsigned temp=1;
            $display("*** test_sim.");
            tb_test_name="test_sim";
            //**test***
            test_no_sbf(100000,temp);
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
    
//***task automatic test_no_sbf***
//  Random input events are generated, but no
//  errors are forced.
//  Returns 0 if test fails and 1 if test passes
    task automatic test_no_sbf(input int n_tries, output int rval);
        begin
            int tmp=0;
            $display("*** test_no_sbf");
            tb_test_name="test_no_sbf";
            //**test***
            for(int i=0;i<n_tries;i++) begin
                prot_reg_d = $urandom();
                #CLK_PERIOD;
                //check results
                if(tb_error_o!=0) begin
                    tmp=1;
                end
            end
            //check results
            if(tmp!=0) begin
                $error("FAIL test_no_sbf. SEU detected but no SEU has been generated");
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
//  single bit-flip faults.
//  Returns 0 if test fails and 1 if test passes
    task automatic test_meu(input int n_tries, output int rval);
        begin
            int tmp=0;
            $display("*** test_meu");
            tb_test_name="test_meu";
            //**test***
            for(int i=0;i<n_tries;i++) begin
                valid_value = $urandom();
                upset_value = valid_value ^ (1<< $urandom_range(0,TB_IN_WIDTH-1));
                //Ensure that the upset actually changes the value
                while(upset_value == valid_value) begin
                    upset_value = valid_value ^ (1<< $urandom_range(0,TB_IN_WIDTH-1));
                end
                //Assign input value
                prot_reg_d = valid_value;
                #CLK_PERIOD;
                //Force error within register
                force prot_reg = upset_value;
                #CLK_PERIOD;
                //check for errors
                if(tb_error_o!=1) begin
                    tmp=1;
                end
                //Release forced error after one cycle
                release prot_reg;
                #CLK_PERIOD;
            end
            //check results
            if(tmp!=0) begin
                $error("FAIL test_meu.Some SBF have not been detected");
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
        prot_reg_d <='{default:0};
        valid_value <='{default:0};
        upset_value <='{default:0};
        if (TB_IN_WIDTH >32) begin
                $error("Width too big");
                `START_RED_PRINT
                $display("TB designed for TB_IN_WIDTH up to 32 bit");
                `END_COLOR_PRINT
        end
        init_sim();
        init_dump();
        reset_dut();
        test_sim();
        $finish;
    end

endmodule
`default_nettype wire

/* -----------------------------------------------
* Project Name   : crossbar research 
* File           : tb_crossbar.v
* Organization   : Barcelona Supercomputing Center
* Author(s)      : Guillem cabo 
* Email(s)       : guillem.cabo@bsc.es
* References     : 
* -----------------------------------------------
* Revision History
*  Revision   | Author    | Commit | Description
*  0.0        | G.cabo    | b571d  | Initial commit
* -----------------------------------------------
*/

//-----------------------------------------------------
// Function   : Simple directed tests
// Description: Show intendend behaviour for default config of DUT

`timescale 1 ns / 1 ns
`default_nettype none
`include "colors.vh"
//***Headers***
//***Test bench***
module tb_crossbar();
//***Parameters***
    parameter CLK_PERIOD      = 2;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
//***DUT parameters***    
    parameter TB_SOC_EVENTS = 32;
    parameter TB_PMU_EVENTS = 24;
    localparam N_BITS_CFG = $clog2(TB_SOC_EVENTS);
//***Signals***
    reg     tb_clk_i ;
    reg     tb_rstn_i ;
    reg     tb_vector_i [0:TB_SOC_EVENTS-1];
    wire     tb_vector_o [0:TB_PMU_EVENTS-1];
    reg     [N_BITS_CFG-1:0] tb_cfg_i  [0:TB_PMU_EVENTS-1]; 
//store name of test for easier debug of waveform
reg[64*8:0] tb_test_name;
reg tb_fail = 0;
//***Module***
    crossbar #(
        .N_OUT(TB_PMU_EVENTS),
        .N_IN(TB_SOC_EVENTS)
    )
        dut_crossbar(
        .clk_i         (tb_clk_i ),
        .rstn_i         (tb_rstn_i ),
        .vector_i (tb_vector_i),
        .vector_o (tb_vector_o),
        .cfg_i (tb_cfg_i)
    );

//***clk_gen***
    initial tb_clk_i = 1;
    always #CLK_HALF_PERIOD tb_clk_i = !tb_clk_i;

//***task automatic reset_dut***
    task automatic reset_dut;
        begin
            tb_test_name="reset_dut";
            $display("*** Toggle reset.");
            tb_rstn_i <= 1'b0; 
            #CLK_PERIOD;
            tb_rstn_i <= 1'b1;
            #CLK_PERIOD;
            $display("Done");
        end
    endtask 

//***task automatic init_sim***
//Initialize TB registers to a known state. Assumes good host
task automatic init_sim;
        begin
            tb_test_name="init_sim";
            $display("*** init sim.");
            //*** TODO ***
            tb_clk_i <='{default:1};
            tb_rstn_i<='{default:0};
            tb_vector_i <='{default:0};
            tb_cfg_i <= '{default:0};
            $display("Done");
        end
    endtask

//***task automatic init_dump***
    task automatic init_dump;
        begin
            tb_test_name="init_dump";
            $dumpfile("crossbar_test.vcd");
            $dumpvars(0,dut_crossbar);
        end
    endtask 

//***task automatic route_ito***
    // This taks takes two parameters. First parameter
    // is the input event. The second parameter is the 
    // selected output. The function enables the input
    // sets the configuration register and checks if
    // the signal reaches the output.
    task automatic route_ito (input int in, out, output int tb_fail);
        begin
            tb_test_name="route_ito";
            //set all other signals to 0
            tb_vector_i <='{default:0};
            //enable signal that we want to route
            #CLK_PERIOD;
            tb_vector_i[in] = 1;
            //clear previous configuration
            tb_cfg_i <= '{default:0};
            #CLK_PERIOD;
            //set new configuration
            tb_cfg_i[out] <= in;
            #CLK_PERIOD;
            #CLK_PERIOD;
            //check if the output signal is enabled
            if(tb_vector_o[out]!=1) begin
                tb_fail = 1; 
                `START_RED_PRINT
                $error("FAIL.%d routed to %d. Expected output value is 1", in, out); 
                `END_COLOR_PRINT
            end

        end
    endtask 

//***task automatic test_sim***
    task automatic test_sim;
        begin
            integer rval;
            integer test_fail;
            
            // try all the input and output combinations
            integer i; //inputs iterator
            integer j; // output iterator
            for(i=0;i<TB_SOC_EVENTS;i++) begin
                for(j=0;j<TB_PMU_EVENTS;j++) begin
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

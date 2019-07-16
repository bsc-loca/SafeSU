//-----------------------------------------------------
// ProjectName: MCCU research 
// Function   : Shows intended behaviour 
// Description: This TB is not used to debug and verify just to show the
//              intended behaviour. Intended to be used with QuestaSim.
// Coder        : G.Cabo

//***Headers***
//***Test bench***
module tb_MCCU();
//***Parameters***
    parameter CLK_PERIOD      = 2;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
//***Signals***
    reg  tb_clk_i ;
    reg tb_rstn_i ;
//***Module***
    MCCU #(
    )
        dut_MCCU(
        .clk_i         (tb_clk_i ),
        .rstn_i         (tb_rstn_i )
    );

//***clk_gen***
    //*** TODO ***
    //initial tb_clk_i = 0;
    //always #CLK_HALF_PERIOD tb_clk_i = !tb_clk_i;

//***task reset_dut***
    task reset_dut;
        begin
            $display("*** Toggle reset.");
            //*** TODO ***
        end
    endtask

//***task init_sim***
    task init_sim;
        begin
            $display("*** init sim.");
            //*** TODO ***
        end
    endtask

//***task init_dump***
    task init_dump;
        begin
            $dumpfile("MCCU_test.vcd");
            $dumpvars(0,dut_MCCU);
        end
    endtask

//***task test_sim***
    task test_sim;
        begin
            $display("*** test_sim.");
            //***Handcrafted test***
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

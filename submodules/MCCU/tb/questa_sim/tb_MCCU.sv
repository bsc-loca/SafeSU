/* -----------------------------------------------
* Project Name   : MCCU research 
* File           : tb_MCCU.v
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
// Function   : Shows intended behaviour 
// Description: This TB is not used to debug and verify just to show the
//              intended behaviour. Designed to be used with QuestaSim.
`timescale 1 ns / 1 ns
`default_nettype none
`include "colors.vh"
//***Headers***
//***Test bench***
module tb_MCCU();
//***Parameters***
    parameter CLK_PERIOD      = 2;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
//***DUT parameters***    
    parameter TB_DATA_WIDTH = 32;
    parameter TB_WEIGHTS_WIDTH = 8;
    parameter TB_N_CORES = 4;
    parameter TB_CORE_EVENTS = 2;
//***Signals***
    reg     tb_clk_i ;
    reg     tb_rstn_i ;
    reg     tb_enable_i;
    reg     [TB_CORE_EVENTS-1:0] tb_events_i [0:TB_N_CORES-1];
    reg     [TB_DATA_WIDTH-1:0] tb_quota_i [0:TB_N_CORES-1];
    reg     [TB_WEIGHTS_WIDTH-1:0] tb_events_weights_i [0:TB_N_CORES-1]
                                               [0:TB_CORE_EVENTS-1];
    reg     tb_update_quota_i [0:TB_N_CORES-1];
    wire    [TB_DATA_WIDTH-1:0] tb_quota_o [0:TB_N_CORES-1];
    wire    tb_interruption_quota_o[TB_N_CORES-1:0];
//store name of test for easier debug of waveform
reg[64*8:0] tb_test_name;
reg tb_fail = 0;
//***Module***
    MCCU #(
        .DATA_WIDTH(TB_DATA_WIDTH),
        .WEIGHTS_WIDTH(TB_WEIGHTS_WIDTH),
        .N_CORES(TB_N_CORES),
        .CORE_EVENTS(TB_CORE_EVENTS)
    )
        dut_MCCU(
        .clk_i         (tb_clk_i ),
        .rstn_i         (tb_rstn_i ),
        .enable_i   (tb_enable_i),
        .events_i (tb_events_i),
        .quota_i (tb_quota_i),
        .update_quota_i(tb_update_quota_i),
        .quota_o (tb_quota_o),
        .events_weights_i(tb_events_weights_i),
        .interruption_quota_o(tb_interruption_quota_o)
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
//Initialize TB registers to a known state. Assumes good host
task automatic init_sim;
        begin
            $display("*** init sim.");
            //*** TODO ***
            tb_clk_i <='{default:1};
            tb_rstn_i<='{default:0};
            tb_enable_i <='{default:0};
            tb_events_i <='{default:0};
            tb_quota_i <= '{default:0};
            tb_events_weights_i <= '{default:0};
            tb_update_quota_i <= '{default:0};
            $display("Done");
        end
    endtask

//***task automatic init_dump***
    task automatic init_dump;
        begin
            $dumpfile("MCCU_test.vcd");
            $dumpvars(0,dut_MCCU);
        end
    endtask 
//***task automatic test_0weigths_1ev***
    //Set weigths,quotas and events. Then check for interrupt
    task automatic test_weigths_ev_quota  (input int weights_i , input events_i, input int quota_i, input intr_o); ;
        begin
            int tmp =0;
            disable_MCCU;
            //rise all events
            if(events_i) begin 
                rise_event(0,0);
                rise_event(1,0);
                rise_event(2,0);
                rise_event(3,0);
                rise_event(0,1);
                rise_event(1,1);
                rise_event(2,1);
                rise_event(3,1);
            end else begin
                release_event(0,0);
                release_event(1,0);
                release_event(2,0);
                release_event(3,0);
                release_event(0,1);
                release_event(1,1);
                release_event(2,1);
                release_event(3,1);
            end
            //Core_id, Singal ID, weight
            set_weight(0,0,weights_i);
            set_weight(1,0,weights_i);
            set_weight(2,0,weights_i);
            set_weight(3,0,weights_i);
            set_weight(0,1,weights_i);
            set_weight(1,1,weights_i);
            set_weight(2,1,weights_i);
            set_weight(3,1,weights_i);
            //Set quota for each core
            set_quota(quota_i,0);
            set_quota(quota_i,1);
            set_quota(quota_i,2);
            set_quota(quota_i,3);
            enable_MCCU();
            #CLK_PERIOD;
            #CLK_PERIOD;
            #CLK_PERIOD;
            get_interrupt(0,tmp);
            $display("interrupt value is %d",tmp);
            if(tmp!=intr_o) begin
                tb_fail = 1; 
                $error("FAIL test_sim. Expected interrupt %d", intr_o);
                `START_RED_PRINT
                $display("FAIL");
                $display("%s",tb_test_name);
                `END_COLOR_PRINT
            end
            get_interrupt(1,tmp);
            $display("interrupt value is %d",tmp);
            if(tmp!=intr_o) begin
                tb_fail = 1; 
                $error("FAIL test_sim. Expected interrupt %d", intr_o);
                `START_RED_PRINT
                $display("FAIL");
                $display("%s",tb_test_name);
                `END_COLOR_PRINT
            end
            get_interrupt(2,tmp);
            $display("interrupt value is %d",tmp);
            if(tmp!=intr_o) begin
                tb_fail = 1; 
                $error("FAIL test_sim. Expected interrupt %d", intr_o);
                `START_RED_PRINT
                $display("FAIL");
                $display("%s",tb_test_name);
                `END_COLOR_PRINT
            end
            get_interrupt(3,tmp);
            $display("interrupt value is %d",tmp);
            if(tmp!=intr_o) begin
                tb_fail = 1; 
                $error("FAIL test_sim. Expected interrupt %d", intr_o);
                `START_RED_PRINT
                $display("FAIL");
                $display("%s",tb_test_name);
                `END_COLOR_PRINT
            end
        end
    endtask 

//***task automatic test_sim***
    task automatic test_sim;
        begin
            int unsigned temp;
            int unsigned c1_id=0;
            int unsigned c1_s1=0;
            int unsigned q_val=150;
            $display("*** test_sim.");
            tb_test_name="test_sim";
            //***Handcrafted test***
            enable_MCCU;
            set_quota(q_val,c1_id);
            #CLK_PERIOD;
            get_remaining_quota(c1_id,temp);
            if(temp!=q_val) begin
                tb_fail = 1; 
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",q_val,temp);
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
            set_quota(200,c1_id);
            #CLK_PERIOD;
            disable_MCCU;
            get_remaining_quota(c1_id,temp);
            if(temp!=200) begin
                tb_fail = 1; 
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",200,temp);
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
            #CLK_PERIOD;
            set_weight(c1_id,c1_s1,10);
            #CLK_PERIOD;
            //quota shall remain 200
            rise_event(c1_id,c1_s1);
            #CLK_PERIOD;
            get_remaining_quota(c1_id,temp);
            if(temp!=200) begin
                tb_fail = 1; 
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",200,temp);
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
            //quota shall decrease to 190 
            enable_MCCU;
            rise_event(c1_id,c1_s1);
            #CLK_PERIOD;
            get_remaining_quota(c1_id,temp);
            if(temp!=190) begin
                tb_fail = 1; 
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",190,temp);
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
            //quota shall decrease to 180 
            release_event(c1_id,c1_s1);
            #CLK_PERIOD;
            get_remaining_quota(c1_id,temp);
            if(temp!=180) begin
                tb_fail = 1; 
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",180,temp);
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
            #CLK_PERIOD;
            reset_dut;
            #CLK_PERIOD;
            //quota sall be 0
            get_remaining_quota(c1_id,temp);
            if(temp!=0) begin
                tb_fail = 1; 
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",0,temp);
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
            #CLK_PERIOD;
            //interrupt shall be risen quota shall remain 0
            rise_event(c1_id,c1_s1);
            #CLK_PERIOD;
            get_remaining_quota(c1_id,temp);
            if(temp!=0) begin
                tb_fail = 1; 
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",0,temp);
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
            get_interrupt(c1_id,temp);
            $display("interrupt value is %d",temp);
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
//***task set_quota
    task automatic set_quota;
        input int unsigned quota_i;
        input int unsigned core_i;
        begin
            $display("*** set_quota of core: %d to: %d",core_i,quota_i);
            tb_update_quota_i[core_i] <= 1'b1;       
            tb_quota_i[core_i] = quota_i;       
            #CLK_PERIOD;
            tb_update_quota_i[core_i] <= 1'b0;       
            tb_quota_i[core_i] = quota_i;       
        end
            //if((quota_i>2**TB_DATA_WIDTH))
            //TODO:fix this
            if((quota_i>((2**32)-1)))
            //    $display("***WARNING: quota_i > TB_DATA_WIDTH^2. quota_i=%d",quota_i);
            if((core_i>TB_N_CORES)) begin
                tb_fail = 1; 
                $error("core_i > N_CORES. core_i=%d",core_i);
                `START_RED_PRINT
                $display("FAIL");
                `END_COLOR_PRINT
            end
    endtask 
//***task get_remaining_quota
    task automatic get_remaining_quota;
        input int unsigned core_i;
        output int unsigned value_o;
        value_o = tb_quota_o[core_i]; 
        $display("get quota of core: %d remaining quota: %d",core_i,value_o);
        if((core_i>TB_N_CORES)) begin
                tb_fail = 1; 
            $error("core_i > N_CORES. core_i=%d",core_i);
            `START_RED_PRINT
            $display("FAIL");
            `END_COLOR_PRINT
        end
    endtask
//***task enable_MCCU
    task automatic enable_MCCU; 
        $display("enable MCCU");
        tb_enable_i = 1'b1;
    endtask
//***task disable_MCCU
    task automatic disable_MCCU; 
        $display("disable MCCU");
        tb_enable_i = 1'b0;
    endtask
//***task rise_event
    task automatic rise_event (input int core_i ,signal_i);
        tb_events_i[core_i][signal_i] = 1'b1; 
        $display("rise event: %d of core: %d",signal_i, core_i);
        if((signal_i>TB_CORE_EVENTS)) begin
                tb_fail = 1; 
            $error("signal_i > TB_CORE_EVENTS. signal_i=%d",signal_i);
            `START_RED_PRINT
            $display("FAIL");
            `END_COLOR_PRINT
        end
        if((core_i>TB_N_CORES)) begin
                tb_fail = 1; 
            $error("core_i > N_CORES. core_i=%d",core_i);
            `START_RED_PRINT
            $display("FAIL");
            `END_COLOR_PRINT
        end
    endtask
//***task release_event
    task automatic release_event(input int core_i ,signal_i); 
        tb_events_i[core_i][signal_i] = 1'b0; 
        $display("release event: %d of core: %d",signal_i, core_i);
        if((signal_i>TB_CORE_EVENTS)) begin
                tb_fail = 1; 
            $error("signal_i > TB_CORE_EVENTS. signal_i=%d",signal_i);
            `START_RED_PRINT
            $display("FAIL");
            `END_COLOR_PRINT
        end
        if((core_i>TB_N_CORES)) begin
                tb_fail = 1; 
            $error("core_i > N_CORES. core_i=%d",core_i);
            `START_RED_PRINT
            $display("FAIL");
            `END_COLOR_PRINT
        end
    endtask
//***task set_weight
    task automatic set_weight; 
        input [$clog2(TB_N_CORES)-1:0] core_i;
        input [$clog2(TB_CORE_EVENTS)-1:0] signal_i;
        input [TB_WEIGHTS_WIDTH-1:0] weight_i;
        $display("set quota weight of signal: %d of core: %d to: %d",signal_i,core_i, weight_i);
        tb_events_weights_i [core_i][signal_i] = weight_i;
        if((weight_i>2**TB_WEIGHTS_WIDTH))
            $display("***WARNING: weight_i > TB_WEIGHTS_WIDTH^2. weight_i=%d",weight_i);
        if((signal_i>TB_CORE_EVENTS)) begin
                tb_fail = 1; 
            $error("signal_i > TB_CORE_EVENTS. signal_i=%d",signal_i);
            `START_RED_PRINT
            $display("FAIL");
            `END_COLOR_PRINT
        end
        if((core_i>TB_N_CORES)) begin
                tb_fail = 1; 
            $error("core_i > N_CORES. core_i=%d",core_i);
            `START_RED_PRINT
            $display("FAIL");
            `END_COLOR_PRINT
        end
    
    endtask
//***task get_interrupt
    task automatic get_interrupt;
        input core_i;
        output int unsigned value_o;
        value_o = tb_interruption_quota_o[core_i]; 
        $display("get quota of core: %d remaining quota: %d",core_i,value_o);
        if((core_i>TB_N_CORES)) begin
                tb_fail = 1; 
            $error("core_i > N_CORES. core_i=%d",core_i);
            `START_RED_PRINT
            $display("FAIL");
            `END_COLOR_PRINT
        end

    endtask
//***init_sim***
    initial begin
        init_sim();
        init_dump();
        reset_dut();
        test_sim();
        
        tb_test_name={"t_weigths_ev_quota(0,1,255,0);"};
        test_weigths_ev_quota(.weights_i(0),.events_i(1),.quota_i(255),.intr_o(0));
        tb_test_name={"t_weigths_ev_quota(10,1,255,0);"};
        test_weigths_ev_quota(10,1,255,0);
        
        tb_test_name={"t_weigths_ev_quota(255,1,255,1);"};
        test_weigths_ev_quota(255,1,255,1);
        tb_test_name={"t_weigths_ev_quota(255,0,255,0);"};
        test_weigths_ev_quota(255,0,255,0);
        
        tb_test_name={"t_weigths_ev_quota(2,1,3,1);"};
        test_weigths_ev_quota(2,1,3,1);
        
        tb_test_name={"t_weigths_ev_quota(0,1,0,0);"};
        test_weigths_ev_quota(0,1,0,0);
        
        tb_test_name={"t_weigths_ev_quota(10,0,0,0);"};
        test_weigths_ev_quota(10,0,0,0);
        $finish;
    end
/*
 //name                  ,rstn_i ,enable_i ,events_i      ,quota_i    ,events_weights_i 
  { "Rst          "     ,0      ,0        ,{0,2,0,4}     ,{0,0,0,0} ,{{0,0,0,0},{5,0,0,8},{9,0,11,7},{9,6,11,11}}},
  { "Init         "     ,1      ,0        ,{15,15,7,7}   ,{10,15,20,25} ,{{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16}}},
  { "Delay        "     ,1      ,0        ,{15,15,3,4}   ,{10,15,20,25} ,{{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16}}},
  { "Enable       "     ,1      ,1        ,{13,12,3,4}   ,{10,15,20,25} ,{{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16}}},
  { "Enable       "     ,1      ,1        ,{1,2,3,4}     ,{10,15,20,25} ,{{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16}}},
*/


endmodule
`default_nettype wire

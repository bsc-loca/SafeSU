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

//***Headers***
//***Test bench***
module tb_MCCU();
//***Parameters***
    parameter CLK_PERIOD      = 2;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
//***DUT parameters***    
    parameter TB_DATA_WIDTH = 32;
    parameter TB_WEIGHTS_WIDTH = 7;
    parameter TB_N_CORES = 1;
    parameter TB_CORE_EVENTS = 1;
//***Signals***
    reg     tb_clk_i ;
    reg     tb_rstn_i ;
    reg     tb_enable_i;
    reg     [TB_CORE_EVENTS-1:0] tb_events_i [0:TB_N_CORES-1];
    reg     [TB_DATA_WIDTH-1:0] tb_quota_i [0:TB_N_CORES-1];
    reg     [TB_WEIGHTS_WIDTH-1:0] tb_events_weights_i [0:TB_N_CORES-1]
                                               [0:TB_CORE_EVENTS-1];
    wire    [TB_DATA_WIDTH-1:0] tb_quota_o [0:TB_N_CORES-1];
    wire    tb_interruption_quota_o[TB_N_CORES-1:0];
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
            //TB registers reset, Host could have same reset or not
            //This emulates a wrapper that resets alonf DUT
            tb_enable_i ='{default:0};
            tb_events_i ='{default:0};
            tb_quota_i = '{default:0};
            #CLK_PERIOD;
            tb_rstn_i <= 1'b1;
            #CLK_PERIOD;
            $display("Done");
        end
    endtask 

//***task automatic init_sim***
//when to use this? Is better not use it and handle the reset with hardware
task automatic init_sim;
        begin
            $display("*** init sim.");
            //*** TODO ***
            tb_clk_i <='{default:0};
            tb_rstn_i<='{default:0};
            tb_enable_i <='{default:0};
            tb_events_i <='{default:0};
            tb_quota_i <= '{default:0};
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

//***task automatic test_sim***
    task automatic test_sim;
        begin
            int unsigned temp;
            int unsigned c1_id=0;
            int unsigned c1_s1=0;
            int unsigned q_val=150;
            $display("*** test_sim.");
            //***Handcrafted test***
            enable_MCCU;
            set_quota(q_val,c1_id);
            get_remaining_quota(c1_id,temp);
            #CLK_PERIOD;
            if(temp!=q_val)
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",q_val,temp);
            set_quota(200,c1_id);
            disable_MCCU;
            get_remaining_quota(c1_id,temp);
            if(temp!=200)
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",200,temp);
            #CLK_PERIOD;
            //set_weight(c1_id,c1_s1,value);//works
            set_weight(c1_id,c1_s1,10);
            //set_weight(2'b10,1'b0,7'b11111111);//works
            //set_weight(2,0,101);//works
            #CLK_PERIOD;
            //quota shall remain 200
            rise_event(c1_id,c1_s1);
            get_remaining_quota(c1_id,temp);
            if(temp!=200)
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",200,temp);
            #CLK_PERIOD;
            //quota shall decrease to 190 
            enable_MCCU;
            rise_event(c1_id,c1_s1);
            get_remaining_quota(c1_id,temp);
            if(temp!=190)
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",190,temp);
            #CLK_PERIOD;
            //quota sall be 0
            reset_dut;
            get_remaining_quota(c1_id,temp);
            if(temp!=0)
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",0,temp);
            #CLK_PERIOD;
            //interrupt shall be risen quota shall remain 0
            rise_event(c1_id,c1_s1);
            get_remaining_quota(c1_id,temp);
            if(temp!=0)
                $error("FAIL test_sim.\n Expected remaining_quota %d,\
                obtained %d",0,temp);
            get_interrupt(c1_id,temp);
            $display("interrupt value is %d",temp);
            if(temp!=1)
                $error("FAIL test_sim. Expected interruption high");
            $display("Done");
        end
    endtask 
//***task set_quota
    task automatic set_quota;
        input int unsigned quota_i;
        input int unsigned core_i;
        begin
            $display("*** set_quota of core: %d to: %d",core_i,quota_i);
            tb_quota_i[core_i] = quota_i;       
        end
            //if((quota_i>2**TB_DATA_WIDTH))
            //TODO:fix this
            if((quota_i>((2**32)-1)))
            //    $display("***WARNING: quota_i > TB_DATA_WIDTH^2. quota_i=%d",quota_i);
            if((core_i>TB_N_CORES)) begin
                $error("core_i > N_CORES. core_i=%d",core_i);
                $display("FAIL");
            end
    endtask 
//***task enable_MCCU
    task automatic enable_MCCU; 
        $display("enable MCCU");
        tb_enable_i <= 1'b1;
    endtask
//***task disable_MCCU
    task automatic disable_MCCU; 
        $display("disable MCCU");
        tb_enable_i <= 1'b0;
    endtask
//***task rise_event
    task automatic rise_event; 
        input core_i;
        input signal_i;
        tb_events_i[core_i][signal_i] = 1'b1; 
        $display("rise core: %d of core: %d",core_i,signal_i);
        if((signal_i>TB_CORE_EVENTS)) begin
            $error("signal_i > TB_CORE_EVENTS. signal_i=%d",signal_i);
            $display("FAIL");
        end
        if((core_i>TB_N_CORES)) begin
            $error("core_i > N_CORES. core_i=%d",core_i);
            $display("FAIL");
        end
    endtask
//***task release_event
    task automatic release_event; 
        input core_i;
        input signal_i;
        tb_events_i[core_i][signal_i] = 1'b0; 
        $display("release core: %d of core: %d",core_i,signal_i);
        if((signal_i>TB_CORE_EVENTS)) begin
            $error("signal_i > TB_CORE_EVENTS. signal_i=%d",signal_i);
            $display("FAIL");
        end
        if((core_i>TB_N_CORES)) begin
            $error("core_i > N_CORES. core_i=%d",core_i);
            $display("FAIL");
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
            $error("signal_i > TB_CORE_EVENTS. signal_i=%d",signal_i);
            $display("FAIL");
        end
        if((core_i>TB_N_CORES)) begin
            $error("core_i > N_CORES. core_i=%d",core_i);
            $display("FAIL");
        end
    
    endtask
//***task get_remaining_quota
    task automatic get_remaining_quota;
        input core_i;
        output int unsigned value_o;
        value_o = tb_quota_o[core_i]; 
        $display("get quota of core: %d remaining quota: %d",core_i,value_o);
        if((core_i>TB_N_CORES)) begin
            $error("core_i > N_CORES. core_i=%d",core_i);
            $display("FAIL");
        end
    endtask
//***task get_interrupt
    task automatic get_interrupt;
        input core_i;
        output int unsigned value_o;
        value_o = tb_interruption_quota_o[core_i]; 
        $display("get quota of core: %d remaining quota: %d",core_i,value_o);
        if((core_i>TB_N_CORES)) begin
            $error("core_i > N_CORES. core_i=%d",core_i);
            $display("FAIL");
        end

    endtask
//***init_sim***
    initial begin
        //init_sim();
        init_dump();
        reset_dut();
        test_sim();
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

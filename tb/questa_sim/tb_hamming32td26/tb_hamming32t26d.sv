//-----------------------------------------------------
// ProjectName: De-RISC/SELENE
// Function   : TB for SEC-DEC Hamming encoder and decoder
// Description: This module takes a signals coming from the input of a register,
//              encodes the data in Hamming (16,11) format, registers the coded data and retrieves
//              the error corrected data at the output
//
//              Double error detection signal is only active while the bit-flip is present 
//              in the circuit aka the error signal is NOT holded until it is handled.
//
// Coder      : G.Cabo
// References : Ben Eater "What is error correction? Hamming codes in hardware" YT 

`timescale 1 ns / 1 ns
`default_nettype none
`include "colors.vh"
//***Headers***
//***Test bench***
module tb_hamming32t26d();
//***Parameters***
    parameter CLK_PERIOD      = 8;
    parameter CLK_HALF_PERIOD = CLK_PERIOD / 2;
    parameter CLK_QUARTER_PERIOD = CLK_HALF_PERIOD/ 2;
    localparam TB_DATA_WIDTH = 26;
    localparam TB_HAM_WIDTH = 32;//Width of data with Hamming check bits
//***DUT parameters***    
    reg     tb_clk_i;
    reg     tb_rstn_i;
    reg     tb_error_o;
    reg     tb_ded_error_o;
    reg   [TB_DATA_WIDTH-1:0] tb_din_i;
    wire   [TB_DATA_WIDTH-1:0] tb_dout_o;
    reg [TB_HAM_WIDTH-1:0] prot_reg;
    wire [TB_HAM_WIDTH-1:0] prot_reg_d;
    wire [TB_HAM_WIDTH-1:0] prot_reg_q;
    logic [TB_HAM_WIDTH-1:0] valid_value;
    logic [TB_HAM_WIDTH-1:0] upset_value;
    var trasient=0; // High while a signal has been forced

//store name of test for easier debug of waveform
reg[64*8:0] tb_test_name;
reg tb_fail = 0;
//***Modules***
//encoder
hamming32t26d_enc#(
)dut_hamming32t26d_enc (
    .data_i(tb_din_i),
    .hv_o(prot_reg_d)
);
// Instance of protected register and output wires
always_ff @(posedge tb_clk_i) begin
if(!tb_rstn_i) begin
    prot_reg <= '{default:'0};
end else begin
    prot_reg <= prot_reg_d ;
end
end
assign prot_reg_q = prot_reg;
//decoder
hamming32t26d_dec#(
)dut_hamming32t26d_dec (
    .data_o(tb_dout_o),
    .hv_i(prot_reg_q),
    .ded_error_o(tb_ded_error_o)
);
// Degug only signals
wire [TB_DATA_WIDTH-1:0] dbg_andio;
assign dbg_andio = tb_din_i ^ tb_dout_o;
wire [TB_HAM_WIDTH-1:0] dbg_andhv;
assign dbg_andhv = valid_value ^ upset_value;
//***clk_gen***
initial tb_clk_i = 1;
always #CLK_HALF_PERIOD tb_clk_i = !tb_clk_i;
default clocking @(posedge tb_clk_i); endclocking
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
        tb_rstn_i=0;
        tb_error_o=0;
        tb_din_i<=0;
        prot_reg=0;
        valid_value=0;
        upset_value=0;
    end
endtask

//***task automatic init_dump***
task automatic init_dump;
    begin
        $dumpfile("test.vcd");
        $dumpvars(0,dut_hamming32t26d_enc);
        $dumpvars(0,dut_hamming32t26d_dec);
    end
endtask 

//***task automatic test_sim***
task automatic test_sim;
    begin
        int unsigned temp=1;
        $display("*** test_sim.");
        tb_test_name="test_sim";
        //**test***
        test_no_sbf(500,temp);
        test_sbf(500,temp);
        test_dbf(500,temp);
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
            tb_din_i  <= $urandom();
            #CLK_PERIOD;
            #CLK_PERIOD;
            //check for errors
            if((tb_dout_o!=$past(tb_din_i)) || (tb_ded_error_o!=0)) begin
                tmp=1;
            end
        end
        //check results
        if(tmp!=0) begin
            $error("FAIL test_no_sbf. DED detected or data corrupted");
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
//***task automatic ***
// Generates random valid hamming vectors (32,26)
task automatic rnd_hamming (output logic [TB_HAM_WIDTH-1:0] hv);
    begin
    logic [TB_HAM_WIDTH-1:0] tmp = $urandom();
    
    hv[3] =tmp[0];
    hv[5] =tmp[1];
    hv[6] =tmp[2];
    hv[7] =tmp[3];
    hv[9] =tmp[4];
    hv[10] =tmp[5];
    hv[11] =tmp[6];
    hv[12] =tmp[7];
    hv[13] =tmp[8];
    hv[14] =tmp[9];
    hv[15] =tmp[10];
    hv[17] =tmp[11];
    hv[18] =tmp[12];
    hv[19] =tmp[13];
    hv[20] =tmp[14];
    hv[21] =tmp[15];
    hv[22] =tmp[16];
    hv[23] =tmp[17];
    hv[24] =tmp[18];
    hv[25] =tmp[19];
    hv[26] =tmp[20];
    hv[27] =tmp[21];
    hv[28] =tmp[22];
    hv[29] =tmp[23];
    hv[30] =tmp[24];
    hv[31] =tmp[25];
    
    hv[1] = ^{hv[3],hv[5],hv[7],
                            hv[9],hv[11],hv[13],hv[15],
                            hv[17],hv[19],hv[21],hv[23],
                            hv[25],hv[27],hv[29],hv[31]};

    hv[2] = ^{hv[3],hv[6],hv[7],
                            hv[10],hv[11],hv[14],hv[15],
                            hv[18],hv[19], hv[22],hv[23],
                            hv[26],hv[27], hv[30],hv[31] };


    hv[4] = ^{hv[5],hv[6],hv[7],
                            hv[12],hv[13],hv[14],hv[15],
                            hv[20],hv[21],hv[22],hv[23],
                            hv[28],hv[29],hv[30],hv[31]};
                            
    hv[8] = ^{hv[9],hv[10],hv[11],hv[12],hv[13],hv[14],hv[15],
                             hv[24],hv[25],hv[26],hv[27],hv[28],hv[29],hv[30],hv[31]};

    hv[16] = ^{hv[17],hv[18],hv[19],hv[20],hv[21],hv[22],hv[23],
                             hv[24],hv[25],hv[26],hv[27],hv[28],hv[29],hv[30],hv[31]};

    hv[0] = ^hv[31:1];
    end
endtask
//***task automatic test_sbf***
//  Random input events are generated, along
//  single bit-flip faults.
//  Returns 0 if test fails and 1 if test passes
task automatic test_sbf(input int n_tries, output int rval);
    begin
        int tmp=0;
        $display("*** test_sbf");
        tb_test_name="test_sbf";
        //**test***
        for(int i=0;i<n_tries;i++) begin
            rnd_hamming(valid_value);
            upset_value = valid_value ^ (1<< $urandom_range(0,TB_HAM_WIDTH-1));
            //Ensure that the upset actually changes the value
            while(upset_value == valid_value) begin
                upset_value = valid_value ^ (1<< $urandom_range(0,TB_HAM_WIDTH-1));
            end
            //Assign input value
            tb_din_i <= {valid_value[31:17],valid_value[15:9],valid_value[7:5],valid_value[3]};
            #CLK_PERIOD;
            //Force error within register
            trasient=1;
            force prot_reg = upset_value;
            #CLK_PERIOD;
            //Release forced error after one cycle
            release prot_reg;
            trasient=0;
            #CLK_PERIOD;
            //check for errors
            if(!($stable(tb_dout_o))||(tb_ded_error_o!=0)) begin
                tmp=1;
                $error("FAIL test_sbf.Some SBF have not been corrected or unexpected DED detected");
            end
            end
            //check results
            if(tmp!=0) begin
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
//***task automatic test_dbf***
//  Random input events are generated, along
//  double bit-flip faults.
//  Returns 0 if test fails and 1 if test passes
task automatic test_dbf(input int n_tries, output int rval);
    begin
        int tmp=0;
        $display("*** test_dbf");
        tb_test_name="test_dbf";
        //**test***
        for(int i=0;i<n_tries;i++) begin
            rnd_hamming(valid_value);
            upset_value = valid_value ^ (3<< $urandom_range(0,TB_HAM_WIDTH-2));
            //Ensure that the upset actually changes the value
            while(upset_value == valid_value) begin
                upset_value = valid_value ^ (1<< $urandom_range(0,TB_HAM_WIDTH-1));
            end
            //Assign input value
            tb_din_i <= {valid_value[15:9],valid_value[7:5],valid_value[3]};
            #CLK_PERIOD;
            //Force error within register
            trasient=1;
            force prot_reg = upset_value;
            #CLK_PERIOD;
            //check for errors
            if((tb_ded_error_o!=1)) begin
                $error("FAIL test_dbf.DED undetected");
                tmp=1;
            end
            //Release forced error after one cycle
            release prot_reg;
            trasient=0;
            #CLK_PERIOD;
            end
            //check results
            if(tmp!=0) begin
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
        valid_value <='{default:0};
        upset_value <='{default:0};
        if (TB_DATA_WIDTH >32) begin
                $error("Width too big");
                `START_RED_PRINT
                $display("TB designed for TB_DATA_WIDTH up to 32 bit");
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

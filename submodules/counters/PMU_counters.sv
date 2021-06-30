//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Submodule of the PMU to handle event counters 
// Description: This module contains the adders and registers for the PMU
//              the registers are exposed through the interface to the modules
//              other modules of the PMU and passed through to the PMU wrapper
//              through the module PMU_raw
//
// Coder      : G.Cabo
// References : 

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
module PMU_counters #
	(
		// Width of registers data bus
		parameter integer REG_WIDTH	= 32,
        // Fault tolerance mechanisms (FT==0 -> FT disabled)
        parameter integer FT  = 0,                                           
		// Amount of counters
		parameter integer N_COUNTERS	= 9
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
		// Soft Reset Signal from configuration registeres. This Signal is 
        // Active HIGH
		input wire  softrst_i,
		// Enable Signal from configuration registeres. This Signal is 
        // Active HIGH
		input wire  en_i,
		// Write enable signal. When this signal is high any value in regs_i
        // is feed in to the internal registers. The Wrapper has to  ensure
        // that the propper values are feeded in.
        // rstn_i and softrst_i, have priority over we_i.
        //TODO: Consider if is worth adding acces to individual registers
		input wire  we_i,

        // Input/output wire from registers of the wrapper to PMU_raw internal
        // registers
        input wire [REG_WIDTH-1:0] regs_i [0:N_COUNTERS-1],
        output logic [REG_WIDTH-1:0] regs_o [0:N_COUNTERS-1],
        //external signals from Soc events
        input wire [N_COUNTERS-1:0] events_i,
        // FT (Fault tolerance) interrupt, error detected but not recoverable
        output wire intr_FT2_o
	);
    reg [REG_WIDTH-1:0] slv_reg [0:N_COUNTERS-1] /*verilator public*/;
    wire [REG_WIDTH-1:0] adder_out [0:N_COUNTERS-1] /*verilator public*/;
//-------------Adders with reset
    //Inside the generate loop it creates as many counters as the parameter
    //N_COUNTERS. For each of them one slv_reg is assigned. When a soft reset
    //(softrst_i high) or hard reset (rstn_i) slv_registers are set
    //to 0. If non of this cases happen if the PMU is enabled (en_i high) and
    //the event of the given counter (events_i[k]) is high the counter
    // increases by one.
    genvar i;
    generate
    for (i=0; i<N_COUNTERS; i=i+1) begin
        assign adder_out[i] = (events_i[i] & en_i)? slv_reg[i]+1:slv_reg[i];
        always @(posedge clk_i) begin
            if(rstn_i == 1'b0 ) begin
                    slv_reg[i] <='{default:0};
            end else begin
                if(softrst_i) begin
                    slv_reg[i] <='{default:0};
                end else begin
                    if (we_i) begin
                        slv_reg[i] <= regs_i[i];
                    end else begin
                        slv_reg[i] <= adder_out[i];
                    end
                end
            end
        end
    end
    endgenerate
//Map input and output registers. If no write is active pass the internal
//value, otherwise bypass the write and show the most recent value
    always_comb begin
        if(we_i) begin
        regs_o = regs_i;
        end else begin
        regs_o = adder_out; 
        end
    end
//FT mechanisms and intr
if(FT==0) begin
    assign intr_FT2_o = 1'b0;
end else begin
    //register last we_i in the negative and positive edges of clock
        // For 200MHz, transients of width < 2500ps shall be detected
        // For 500MHz, transients of width < 1000ps shall be detected
        // Expected transients < 900ps
    com_tr #(
		.IN_WIDTH(1)
	)dut_com_tr (
		.clk_i(clk_i),
		.dclk_i(~clk_i),
		.rstn_i(rstn_i),
		.signal_i(we_i),
		.error_o(intr_FT2_o)
	);
end
///////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
    //auxiliar registers
    reg f_past_valid ;
    initial f_past_valid = 1'b0;
    //Set f_past_valid after first clock cycle
    always@( posedge clk_i )
        f_past_valid <= 1'b1;
   
    //assume that if f_past is not valid you have to reset
    always @(*) begin
		if(0 == f_past_valid) begin
            assume(0 == rstn_i);
         end
    end
         
         
   default clocking @(posedge clk_i); endclocking   
  // check that values can increase
   cover property (!we_i[*5] |-> slv_reg[0]==32'h00000003);
   cover property (!we_i[*5] |-> slv_reg[1]==32'h00000003);
   cover property (!we_i[*5] |-> slv_reg[2]==32'h00000003);
   cover property (!we_i[*5] |-> slv_reg[3]==32'h00000003);
   cover property (!we_i[*5] |-> slv_reg[4]==32'h00000003);
   cover property (!we_i[*5] |-> slv_reg[5]==32'h00000003);
   cover property (!we_i[*5] |-> slv_reg[6]==32'h00000003);
   cover property (!we_i[*5] |-> slv_reg[7]==32'h00000003);
   cover property (!we_i[*5] |-> slv_reg[8]==32'h00000003);
  // check that max value can be reached 
   cover property (!we_i[*5] |-> slv_reg[0]==32'hffffffff);
   cover property (!we_i[*5] |-> slv_reg[1]==32'hffffffff);
   cover property (!we_i[*5] |-> slv_reg[2]==32'hffffffff);
   cover property (!we_i[*5] |-> slv_reg[3]==32'hffffffff);
   cover property (!we_i[*5] |-> slv_reg[4]==32'hffffffff);
   cover property (!we_i[*5] |-> slv_reg[5]==32'hffffffff);
   cover property (!we_i[*5] |-> slv_reg[6]==32'hffffffff);
   cover property (!we_i[*5] |-> slv_reg[7]==32'hffffffff);
   cover property (!we_i[*5] |-> slv_reg[8]==32'hffffffff);
   //TODO:Write assertions for:
   //   After a write register must be update and remain stable if no more
   //   writes or events happen

`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip

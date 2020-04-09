//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Integrate PMU features under one module
// Description: Interface agnostic implementation of the  PMU. Values of the
//              PMU are registered in this module.
//              
//              This module is responsible of configure the memory map, handle
//              write / read syncronization with a higher level module that
//              integrates standar bus interfaces such as AXI, AHB or wishbone.
//
//              Parametrization of the features is configured here by
//              replicating instances of features and adjusting basic
//              parameters such as counters width.
//
// Coder      : G.Cabo
// References : Implementation of Maximum-Contention Control Unit (MCCU): 
//              ResourceAccess Count and Contention Time Enforcement. 
//              https://upcommons.upc.edu/handle/2117/133656

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
	module PMU_raw #
	(
        //------------- External parameters 
		// Width of registers data bus
		parameter integer REG_WIDTH	= 32,
		// Amount of counters
		parameter integer N_COUNTERS	= 9,
		// Configuration registers
		parameter integer N_CONF_REGS	= 1,
		// Overflow
		parameter integer OVERFLOW	= 1, //Yes/No
		// Quota
		parameter integer QUOTA	= 0, //Yes/No
		// MCCU - Maximum-contention Control Unit mode
		parameter integer MCCU	= 0, //Yes/No
		// MCCU - N_CORES
		parameter integer N_CORES	= 1,

        //------------- Internal Parameters 
        //---- configuration registers
        localparam BASE_CFG = 0,
        localparam END_CFG = BASE_CFG + N_CONF_REGS -1,
        //---- Counter registers
        localparam BASE_COUNTERS = END_CFG + 1,
        localparam END_COUNTERS = BASE_COUNTERS + N_COUNTERS-1, 
        //---- Quota interruption  registers
            // General parameters feature  
        localparam BASE_OVERFLOW_INTR = END_COUNTERS + 1,
            // mask feature
            // OVERFLOW_INTR_MASK_REGS is equivalent to $ceil(N_COUNTERS/REG_WIDTH)
        localparam BASE_OVERFLOW_MASK = BASE_OVERFLOW_INTR,
        localparam N_OVERFLOW_MASK_REGS = ((N_COUNTERS-1)/REG_WIDTH+1), 
        localparam END_OVERFLOW_MASK = BASE_OVERFLOW_MASK + N_OVERFLOW_MASK_REGS -1,
            // overflow interruption vector feature
            // OVERFLOW_INTR_MASK_REGS is equivalent to $ceil(N_COUNTERS/REG_WIDTH)
        localparam BASE_OVERFLOW_VECT = (END_OVERFLOW_MASK+1),
        localparam N_OVERFLOW_VECT_REGS = ((N_COUNTERS-1)/REG_WIDTH+1), 
        localparam END_OVERFLOW_VECT = BASE_OVERFLOW_VECT + N_OVERFLOW_VECT_REGS -1,
            // General parameters feature  
        localparam N_OVERFLOW_REGS = (N_OVERFLOW_VECT_REGS + N_OVERFLOW_VECT_REGS) * OVERFLOW,
        localparam END_OVERFLOW_INTR = BASE_OVERFLOW_INTR + N_OVERFLOW_REGS -1,
            // Total of registers used
        localparam integer TOTAL_NREGS =
                                    N_COUNTERS + N_CONF_REGS + N_OVERFLOW_REGS
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
        // Input/output wire from registers of the wrapper to PMU_raw internal
        // registers
        input wire [REG_WIDTH-1:0] regs_i [0:TOTAL_NREGS-1],
        output wire [REG_WIDTH-1:0] regs_o [0:TOTAL_NREGS-1],
        // Wrapper writte enable, prevents slaves to write in to registers and
        // uploads the content with external values
        input wire wrapper_we_i,
        // Event signals
        input wire [N_COUNTERS-1:0] events_i,
        //interruption rises when one of the counters overflows
        output reg intr_overflow_o

/*        //interruptions risen when one event exceeds it expected max duration
        output wire int_rdc_o,
        //interruptions risen when cores exceeds the quota of MCCU
        output wire MCCU_int_o [N_CORES-1:0],
        //interruption rises when the total of cuota consumed is exceeded
        output wire int_quota_o,
        //external signals from Soc events
        input wire [N_COUNTERS-1:0] events_i, // bus of signals for counters 
        // Input/output wire from registers of the wrapper to PMU_raw internal
        // registers
        input wire [REG_WIDTH-1:0] regs_i [0:TOTAL_NREGS-1],
        output wire [REG_WIDTH-1:0] regs_o [0:TOTAL_NREGS-1],
        // Wrapper writte addres
        input wire [REG_ID_WIDTH-1:0] wrapper_wa_i
*/        
	);
//----------------------------------------------
//------------- Declare wires from/to  wrapper registers
//----------------------------------------------
    //---- configuration signals
    reg [REG_WIDTH-1:0] cfg_reg;
    wire en_i;
    wire softrst_i;
    //---- Counter signals
    wire [REG_WIDTH-1:0] counter_regs_o [0 : N_COUNTERS-1];
    wire [REG_WIDTH-1:0] counter_regs_int [0 : N_COUNTERS-1];
    //---- Overflow interruption  signals
    wire [N_COUNTERS-1:0] overflow_intr_mask_i [0 : N_OVERFLOW_MASK_REGS-1]; 
    wire [N_COUNTERS-1:0] overflow_intr_vect_o [0 : N_OVERFLOW_VECT_REGS-1];
     
//----------------------------------------------
//------------- Map registers from wrapper to slave functions
//----------------------------------------------
    //---- configuration registers
    always_ff @(posedge clk_i, negedge rstn_i) begin
        if(rstn_i == 1'b0 ) begin
            cfg_reg <= {REG_WIDTH{1'b0}};
        end else begin
            cfg_reg <= regs_i [BASE_CFG];
        end
    end
    assign en_i = regs_i [BASE_CFG][0];
    assign softrst_i = regs_i [BASE_CFG][1];
    //Send content to wrapper
    assign regs_o[BASE_CFG] = cfg_reg;
    
    //---- Counter registers
    genvar x;
    generate
        for(x=BASE_COUNTERS;x<=END_COUNTERS;x++) begin
            assign counter_regs_int[x-BASE_COUNTERS] = regs_i[x];
            assign regs_o[x] = counter_regs_o[x-BASE_COUNTERS];
        end
    endgenerate
    //---- Overflow interruption  registers
    generate
        for(x=0;x<N_OVERFLOW_MASK_REGS;x++) begin
            assign overflow_intr_mask_i[x] = (rstn_i == 1'b0)? '{default:0} :regs_i [x][N_COUNTERS-1:0];
        end
        for(x=BASE_OVERFLOW_VECT;x<=END_OVERFLOW_VECT;x++) begin
            assign regs_o [x] = (rstn_i == 1'b0)? '{default:0} : REG_WIDTH'(overflow_intr_vect_o[x-BASE_OVERFLOW_VECT]);
        end
    endgenerate
    //---- Quota interruption  registers
    //---- MCCU  registers
    //---- Request Duration Counter (RDC) registers 

//----------------------------------------------
//------------- Counters instance
//----------------------------------------------
    PMU_counters # (
		.REG_WIDTH	(REG_WIDTH),
		.N_COUNTERS	(N_COUNTERS)
	)
    inst_counters (
		.clk_i      (clk_i),
		.rstn_i     (rstn_i),
		.softrst_i  (softrst_i),
		.en_i       (en_i),
		.we_i       (wrapper_we_i),
        .regs_i     (counter_regs_int),
        .regs_o     (counter_regs_o),
        .events_i   (events_i) 
	);

//----------------------------------------------
//------------- Overflow interuption instance
//----------------------------------------------
    PMU_overflow # (
		.REG_WIDTH	(REG_WIDTH),
		.N_COUNTERS	(N_COUNTERS)
	)
    inst_overflow (
		.clk_i              (clk_i),
		.rstn_i             (rstn_i),
		.softrst_i          (softrst_i),
		.en_i               (en_i),
        .counter_regs_i     (counter_regs_o),
        .over_intr_mask_i   (overflow_intr_mask_i[0][N_COUNTERS-1:0]), 
        .intr_overflow_o    (intr_overflow_o), 
        .over_intr_vect_o   (overflow_intr_vect_o[0][N_COUNTERS-1:0])
	);

//----------------------------------------------
//------------- Quota interruption instance
//----------------------------------------------
/*    PMU_quota # (
        .REG_WIDTH	(REG_WIDTH),
        .N_COUNTERS	(N_COUNTERS)
    )
    inst_quota(
        .clk_i          (),
        .rstn_i         (),
        .counter_value_i(),
        .softrst_i      (),
        .quota_limit_i  (),
        .quota_mask_i   (), 
        .intr_quota_o   () 
    );
*/
//----------------------------------------------
//------------- MCCU instance
//----------------------------------------------
/*    MCCU # (
        // Width of data registers
        .DATA_WIDTH     (MCCU_DATA_WIDTH),
        // Width of weights registers
        .WEIGHTS_WIDTH  (MCCU_WEIGHTS_WIDTH),
        //Cores. Change this may break Verilator TB
        .N_CORES        (MCCU_N_CORES),
        //Signals per core. Change this may break Verilator TB
        .CORE_EVENTS    (MCCU_CORE_EVENTS)
    )
    inst_MCCU(
        .clk_i                  (clk_i),
        .rstn_i                 (rstn_i || MCCU_rstn_int),
        .enable_i               (MCCU_enable_int),// Software map
        .events_i               (events_int),//how to parametrize this? new parameter on top or up to the programer that does the integration?
        .quota_i                (MCCU_quota_int),//One register per core
        .update_quota_i         (MCCU_update_quota_int),//Software map
        .quota_o                (MCCU_quota_o),//write back to a read register
        .events_weights_i       (MCCU_events_weights_int),//core_events times WEIGHTS_WIDTH registers
        .interruption_quota_o   (MCCU_int_o)//N_CORES output signals Add this to top or single toplevel interrupt and an interrupt vector that identifies the source?
                                   // Individual interrupts allow each core to
                                   // handle their own interrupts , therefore
                                   //it seems to be te right solution.
    );
*/
//----------------------------------------------
//------------- Request Duration Counter (RDC) 
//----------------------------------------------
/*    
    RDC #(
        // Width of data registers
        .DATA_WIDTH     (MCCU_DATA_WIDTH),
        // Width of weights registers
        .WEIGHTS_WIDTH  (MCCU_WEIGHTS_WIDTH),
        //Cores. 
        .N_CORES        (MCCU_N_CORES),
        //Signals per core. 
        .CORE_EVENTS    (MCCU_CORE_EVENTS)
    ) inst_RDC(
        .clk_i                  (clk_i),
        .rstn_i                 (rstn_i || MCCU_rstn_int ),
        .enable_i               (MCCU_enable_int),// Software map
        .events_i               (events_int),//how to parametrize this? new parameter on top or up to the programer that does the integration?
        .events_weights_i       (MCCU_events_weights_int),//core_events times WEIGHTS_WIDTH registers
        .interruption_rdc_o(intr_rdc_o),// interruption signaling a signal has exceed the expected maximum request time
        .interruption_vector_rdc_o(intrv_rdc_int) // vector with offending
            //signals. One hot encoding.
            //Cleared when MCCU is disabled.
    );
*/
/////////////////////////////////////////////////////////////////////////////////
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


`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip


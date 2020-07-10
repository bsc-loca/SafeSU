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

        //------------- Internal Parameters 
		
        // *** Active functions and global configuration
        //---- Overflow
		localparam integer OVERFLOW	= 1, //Yes/No
		//---- Quota
		localparam integer QUOTA	= 1, //Yes/No
		//---- MCCU - Maximum-contention Control Unit mode
		localparam integer MCCU	= 1, //Yes/No
		//---- RDC - Request Duration Counters
		localparam integer RDC	= 1, //Yes/No
       
        // *** Memory map related features
        
        //---- Main configuration registers
        localparam BASE_CFG = 0,
        localparam END_CFG = BASE_CFG + N_CONF_REGS -1,
        
        //---- Counter registers
        localparam BASE_COUNTERS = END_CFG + 1,
        localparam END_COUNTERS = BASE_COUNTERS + N_COUNTERS-1, 
        
        //---- Overflow interruption  registers
            // General parameters feature  
        localparam BASE_OVERFLOW_INTR = END_COUNTERS + 1,
            // mask feature
            // OVERFLOW_INTR_MASK_REGS is equivalent to $ceil(N_COUNTERS/REG_WIDTH)
        localparam BASE_OVERFLOW_MASK = BASE_OVERFLOW_INTR,
        localparam N_OVERFLOW_MASK_REGS = ((N_COUNTERS-1)/REG_WIDTH+1), 
        localparam END_OVERFLOW_MASK = BASE_OVERFLOW_MASK + N_OVERFLOW_MASK_REGS -1,
            // overflow interruption vector feature
            // OVERFLOW_INTR_VECT_REGS is equivalent to $ceil(N_COUNTERS/REG_WIDTH)
        localparam BASE_OVERFLOW_VECT = (END_OVERFLOW_MASK+1),
        localparam N_OVERFLOW_VECT_REGS = ((N_COUNTERS-1)/REG_WIDTH+1), 
        localparam END_OVERFLOW_VECT = BASE_OVERFLOW_VECT + N_OVERFLOW_VECT_REGS -1,
            // General parameters overflow feature  
        localparam N_OVERFLOW_REGS = (N_OVERFLOW_VECT_REGS + N_OVERFLOW_VECT_REGS) * OVERFLOW,
        localparam END_OVERFLOW_INTR = BASE_OVERFLOW_INTR + N_OVERFLOW_REGS -1,
        
        //---- Quota interruption  registers
            // General parameters feature  
        localparam BASE_QUOTA_INTR = END_OVERFLOW_INTR + 1,
            // mask feature
                // QUOTA_INTR_MASK_REGS equivalentto to $ceil(N_COUNTERS/REG_WIDTH)
        localparam BASE_QUOTA_MASK = BASE_QUOTA_INTR,
        localparam N_QUOTA_MASK_REGS = ((N_COUNTERS-1)/REG_WIDTH+1), 
        localparam END_QUOTA_MASK = BASE_QUOTA_MASK + N_QUOTA_MASK_REGS -1,
            // Available quota aka quota limit
        localparam BASE_QUOTA_LIMIT = END_QUOTA_MASK + 1, 
        localparam N_QUOTA_LIMIT_REGS = 1,
        localparam END_QUOTA_LIMIT = BASE_QUOTA_LIMIT + N_QUOTA_LIMIT_REGS -1,
            // General parameters overflow feature  
        localparam N_QUOTA_REGS = (N_QUOTA_MASK_REGS + N_QUOTA_LIMIT_REGS ) * QUOTA,
        localparam END_QUOTA_INTR = BASE_QUOTA_INTR + N_QUOTA_REGS -1,
        
        //---- MCCU registers and parameters
            // General parameters feature
                // Width of the assigned weights for each event
        localparam MCCU_WEIGHTS_WIDTH = 8,
                // Number of cores with MCCU capabilities
        localparam MCCU_N_CORES = 4, 
                // Number of events per core
        localparam MCCU_N_EVENTS = 2 , 
            // Main configuration register for the MCCU 
        localparam BASE_MCCU_CFG = END_QUOTA_INTR + 1,
        localparam N_MCCU_CFG = 1,
        localparam END_MCCU_CFG = BASE_MCCU_CFG + N_MCCU_CFG -1 ,
            // Quota limit assgined to each core
        localparam BASE_MCCU_LIMITS = END_MCCU_CFG +1,
        localparam N_MCCU_LIMITS = MCCU_N_CORES,
        localparam END_MCCU_LIMITS = BASE_MCCU_LIMITS + N_MCCU_LIMITS -1,
            // Currently available Quota for each core
        localparam BASE_MCCU_QUOTA = END_MCCU_LIMITS +1,
        localparam N_MCCU_QUOTA = MCCU_N_CORES,
        localparam END_MCCU_QUOTA = BASE_MCCU_QUOTA + N_MCCU_QUOTA -1,
            // Weights for each one of the available events
        localparam BASE_MCCU_WEIGHTS = END_MCCU_QUOTA + 1,
                // (((....)-1)/(...)+1) is equivalent to ceil
        localparam N_MCCU_WEIGHTS = (((MCCU_N_CORES*MCCU_N_EVENTS*MCCU_WEIGHTS_WIDTH)-1)/REG_WIDTH+1),
        localparam END_MCCU_WEIGHTS = BASE_MCCU_WEIGHTS + N_MCCU_WEIGHTS -1,
            // General parameters feature  
        localparam N_MCCU_REGS = (N_MCCU_CFG + N_MCCU_LIMITS+ N_MCCU_QUOTA + N_MCCU_WEIGHTS) * MCCU,
        
        //---- RDC registers and parameters. Shared with MCCU 
            // General parameters feature
                // Width of the assigned weights for each event
        localparam RDC_WEIGHTS_WIDTH = MCCU_WEIGHTS_WIDTH,
                // Number of cores with RDC capabilities
        localparam RDC_N_CORES = MCCU_N_CORES, 
                // Number of events per core
        localparam RDC_N_EVENTS = MCCU_N_EVENTS, 
            // Interruption vector 
        localparam BASE_RDC_VECT = (END_MCCU_WEIGHTS+1),
                // (((....)-1)/(...)+1) is equivalent to ceil
        localparam N_RDC_VECT_REGS = ((RDC_N_CORES*RDC_N_EVENTS-1)/REG_WIDTH+1), 
        localparam END_RDC_VECT = BASE_RDC_VECT + N_RDC_VECT_REGS -1 ,
            // Weights for each one of the available events. SHARED with MCCU
        localparam BASE_RDC_WEIGHTS = BASE_MCCU_WEIGHTS, 
                // (((....)-1)/(...)+1) is equivalent to ceil
        localparam N_RDC_WEIGHTS = 0, 
        localparam END_RDC_WEIGHTS = END_MCCU_WEIGHTS,
            // General parameters feature  
        localparam N_RDC_REGS = (N_RDC_WEIGHTS + N_RDC_VECT_REGS) * RDC,
        
        //---- Total of registers used
        localparam integer TOTAL_NREGS =
                                    N_COUNTERS + N_CONF_REGS + N_OVERFLOW_REGS
                                    +N_QUOTA_REGS + N_MCCU_REGS + N_RDC_REGS
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
        output wire intr_overflow_o,
        //interruption rises when overall events quota is exceeded 
        output wire intr_quota_o,
        // MCCU interruption for exceeded quota. One signal per core
        output wire [MCCU_N_CORES-1:0] intr_MCCU_o,
        // RDC (Request Duration Counter) interruption for exceeded quota
        output wire intr_RDC_o
	);
    //----------------------------------------------
    // VIVADO: list of debug signals for ILA 
    //----------------------------------------------     
    //`define ILA_DEBUG_PMU_RAW                                 
    `ifdef ILA_DEBUG_PMU_RAW                                                           
    (* MARK_DEBUG = "TRUE" *) logic [REG_WIDTH-1:0] debug_regs_i [0:TOTAL_NREGS-1];
    (* MARK_DEBUG = "TRUE" *) logic [REG_WIDTH-1:0] debug_regs_o [0:TOTAL_NREGS-1]; 
    (* MARK_DEBUG = "TRUE" *) wire debug_wrapper_we_i;              
    (* MARK_DEBUG = "TRUE" *) wire [N_COUNTERS-1:0] debug_events_i;                 
    (* MARK_DEBUG = "TRUE" *) wire debug_intr_overflow_o;                 
    (* MARK_DEBUG = "TRUE" *) wire debug_intr_quota_o;                           
    (* MARK_DEBUG = "TRUE" *) wire [MCCU_N_CORES-1:0] debug_intr_MCCU_o;            
    (* MARK_DEBUG = "TRUE" *) wire debug_intr_RDC_o;            
                                                                                    
    assign debug_regs_i = regs_i;                                                   
    assign debug_regs_o = regs_o;                                                   
    assign debug_wrapper_we_i = wrapper_we_i;                                       
    assign debug_events_i = events_i;                                               
    assign debug_intr_overflow_o = intr_overflow_o;                                 
    assign debug_intr_quota_o = intr_quota_o;                                       
    assign debug_intr_MCCU_o = intr_MCCU_o;                                         
    assign debug_intr_RDC_o = intr_RDC_o;                                           
                                                                                    
    `endif                                                                          
      
//----------------------------------------------
//------------- Declare wires from/to  wrapper registers
//----------------------------------------------
    
    //---- configuration signals
    wire [1:0] selftest_mode;
    wire en_i;
    wire softrst_i;
    wire overflow_en_i;
    wire overflow_softrst_i;
    wire quota_softrst_i;
    //---- Counter signals
    wire [REG_WIDTH-1:0] counter_regs_o [0 : N_COUNTERS-1];
    wire [REG_WIDTH-1:0] counter_regs_int [0 : N_COUNTERS-1];
    //---- Overflow interruption  signals
    wire [N_COUNTERS-1:0] overflow_intr_mask_i [0 : N_OVERFLOW_MASK_REGS-1]; 
    wire [N_COUNTERS-1:0] overflow_intr_vect_o [0 : N_OVERFLOW_VECT_REGS-1];
     
//----------------------------------------------
//------------- Map registers from wrapper to slave functions
//----------------------------------------------
    //Selftest mode. Bypass events and sets internal values
    assign selftest_mode [0] =regs_i [BASE_CFG][30];
    assign selftest_mode [1] =regs_i [BASE_CFG][31];

    //counters
    assign en_i = regs_i [BASE_CFG][0];
    assign softrst_i = regs_i [BASE_CFG][1];
    //overflow
    assign overflow_en_i = regs_i [BASE_CFG][2];
    assign overflow_softrst_i = regs_i [BASE_CFG][3];
    //quota    
    assign quota_softrst_i = regs_i [BASE_CFG][4];
    // Register never set by PMU, only written by master
    genvar y;
    generate
        for(y=BASE_CFG;y<=END_CFG;y++) begin
               assign regs_o[y] = regs_i[y];
        end
    endgenerate
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
            assign overflow_intr_mask_i[x] = (rstn_i == 1'b0)? {N_COUNTERS{1'b0}} :regs_i [x+BASE_OVERFLOW_MASK][N_COUNTERS-1:0];
        end
        for(x=BASE_OVERFLOW_VECT;x<=END_OVERFLOW_VECT;x++) begin
            assign regs_o [x] = (rstn_i == 1'b0)? {REG_WIDTH{1'b0}} : REG_WIDTH'(overflow_intr_vect_o[x-BASE_OVERFLOW_VECT]);
        end
    endgenerate
        // Register never set by PMU, only written by master
    assign regs_o[BASE_OVERFLOW_MASK:END_OVERFLOW_MASK] = regs_i[BASE_OVERFLOW_MASK:END_OVERFLOW_MASK];
    //---- Quota interruption  registers
        // Register never set by PMU, only written by master
    assign regs_o[BASE_QUOTA_MASK:END_QUOTA_MASK] = regs_i[BASE_QUOTA_MASK:END_QUOTA_MASK];
    assign regs_o[BASE_QUOTA_LIMIT:END_QUOTA_LIMIT] = regs_i[BASE_QUOTA_LIMIT:END_QUOTA_LIMIT];
    //---- MCCU  registers
        // Register never set by PMU, only written by master
    assign regs_o[BASE_MCCU_CFG:END_MCCU_CFG] = regs_i[BASE_MCCU_CFG:END_MCCU_CFG];
    assign regs_o[BASE_MCCU_LIMITS:END_MCCU_LIMITS] = regs_i[BASE_MCCU_LIMITS:END_MCCU_LIMITS];
    assign regs_o[BASE_MCCU_WEIGHTS:END_MCCU_WEIGHTS] = regs_i[BASE_MCCU_WEIGHTS:END_MCCU_WEIGHTS];
    //---- Request Duration Counter (RDC) registers 

//----------------------------------------------
//------------- Selftest configuration
//----------------------------------------------
logic [N_COUNTERS-1:0] events_int;

localparam NO_SELF_TEST = 2'b00;
localparam ALL_ACTIVE = 2'b01;
localparam ALL_OFF = 2'b10;
localparam ONE_ON = 2'b11;

always_comb begin
    case (selftest_mode)
        NO_SELF_TEST : begin
            events_int = events_i;
        end
        ALL_ACTIVE : begin
            events_int = {N_COUNTERS{1'b1}};
        end
        ALL_OFF : begin
            events_int = {N_COUNTERS{1'b0}};
        end
        ONE_ON : begin
            events_int[0] = 1'b1;
            events_int[N_COUNTERS-1:1] = {(N_COUNTERS-1){1'b0}};
        end
    endcase
end

//----------------------------------------------
//------------- Counters instance
//----------------------------------------------
//TODO: What happen if we is active but no write is done to the range of the
//counters?
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
        .events_i   (events_int) 
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
		.softrst_i          (overflow_softrst_i),
		.en_i               (overflow_en_i),
        .counter_regs_i     (counter_regs_o),
        .over_intr_mask_i   (overflow_intr_mask_i[0][N_COUNTERS-1:0]), 
        .intr_overflow_o    (intr_overflow_o), 
        .over_intr_vect_o   (overflow_intr_vect_o[0][N_COUNTERS-1:0])
	);

//----------------------------------------------
//------------- Quota interruption instance
//----------------------------------------------
    
    PMU_quota # (
        .REG_WIDTH	(REG_WIDTH),
        .N_COUNTERS	(N_COUNTERS)
    )
    inst_quota(
        .clk_i          (clk_i),
        .rstn_i         (rstn_i),
        .counter_value_i(counter_regs_o),
        .softrst_i      (quota_softrst_i),
        .quota_limit_i  (regs_i[BASE_QUOTA_LIMIT]),
        .quota_mask_i   (regs_i[BASE_QUOTA_MASK][N_COUNTERS-1:0]), 
        .intr_quota_o   (intr_quota_o) 
    );

//----------------------------------------------
//------------- MCCU instance
//----------------------------------------------
    wire MCCU_enable_int;
    assign MCCU_enable_int = regs_i[BASE_MCCU_CFG][0];
    
    wire MCCU_softrst;
    assign MCCU_softrst = regs_i[BASE_MCCU_CFG][1];
    
    
    //NON-PARAMETRIC one bit for each core
    wire MCCU_update_quota_int [0:MCCU_N_CORES-1];
        //core_0
    assign MCCU_update_quota_int[0] = regs_i[BASE_MCCU_CFG][2]; 
        //core_1
    assign MCCU_update_quota_int[1] = regs_i[BASE_MCCU_CFG][3]; 
        //core_2
    assign MCCU_update_quota_int[2] = regs_i[BASE_MCCU_CFG][4]; 
        //core_3
    assign MCCU_update_quota_int[3] = regs_i[BASE_MCCU_CFG][5]; 
    
    //NON-PARAMETRIC Adjust for different MCCU_N_CORES MCCU_CORE_EVENTS
        //eventuall when inputs will be selectable with a crossbar signals can
        //be hardcoded to specific corssbars outputs
    wire [MCCU_N_EVENTS-1:0] MCCU_events_int[0:MCCU_N_CORES-1];
        //core_0
    assign MCCU_events_int [0] = {{events_int[0]},{events_int[1]}};
        //core_1
    assign MCCU_events_int [1] = {{events_int[2]},{events_int[3]}};
        //core_2
    assign MCCU_events_int [2] = {{events_int[4]},{events_int[5]}};
        //core_3
    assign MCCU_events_int [3] = {{events_int[6]},{events_int[7]}};
        
    //NON-PARAMETRIC This can be autogenenerated TODO     
    wire [MCCU_WEIGHTS_WIDTH-1:0] MCCU_events_weights_int [0:MCCU_N_CORES-1]
                                                     [0:MCCU_N_EVENTS-1];
        //core_0
    assign MCCU_events_weights_int [0][0] =  regs_i[BASE_MCCU_WEIGHTS][MCCU_WEIGHTS_WIDTH-1:0];
    assign MCCU_events_weights_int [0][1] =  regs_i[BASE_MCCU_WEIGHTS][2*MCCU_WEIGHTS_WIDTH-1:MCCU_WEIGHTS_WIDTH];
        //core_1
    assign MCCU_events_weights_int [1][0] =  regs_i[BASE_MCCU_WEIGHTS][3*MCCU_WEIGHTS_WIDTH-1:2*MCCU_WEIGHTS_WIDTH];
    assign MCCU_events_weights_int [1][1] =  regs_i[BASE_MCCU_WEIGHTS][4*MCCU_WEIGHTS_WIDTH-1:3*MCCU_WEIGHTS_WIDTH];
        //core_2
    assign MCCU_events_weights_int [2][0] =  regs_i[BASE_MCCU_WEIGHTS+1][MCCU_WEIGHTS_WIDTH-1:0];
    assign MCCU_events_weights_int [2][1] =  regs_i[BASE_MCCU_WEIGHTS+1][2*MCCU_WEIGHTS_WIDTH-1:MCCU_WEIGHTS_WIDTH];
        //core_3
    assign MCCU_events_weights_int [3][0] =  regs_i[BASE_MCCU_WEIGHTS+1][3*MCCU_WEIGHTS_WIDTH-1:2*MCCU_WEIGHTS_WIDTH];
    assign MCCU_events_weights_int [3][1] =  regs_i[BASE_MCCU_WEIGHTS+1][4*MCCU_WEIGHTS_WIDTH-1:3*MCCU_WEIGHTS_WIDTH];
    
    //NON-PARAMETRIC unpack to pack
    wire MCCU_intr_up [MCCU_N_CORES-1:0];
    assign intr_MCCU_o = {{MCCU_intr_up[3]},{MCCU_intr_up[2]}
                        ,{MCCU_intr_up[1]},{MCCU_intr_up[0]}};

    MCCU # (
        // Width of data registers
        .DATA_WIDTH     (REG_WIDTH),
        // Width of weights registers
        .WEIGHTS_WIDTH  (MCCU_WEIGHTS_WIDTH),
        //Cores. Change this may break Verilator TB
        .N_CORES        (MCCU_N_CORES),
        //Signals per core. Change this may break Verilator TB
        .CORE_EVENTS    (MCCU_N_EVENTS)
    )
    inst_MCCU(
        .clk_i                  (clk_i),
        .rstn_i                 (rstn_i || MCCU_softrst),
        .enable_i               (MCCU_enable_int),// Software map
        .events_i               (MCCU_events_int),
        .quota_i                (regs_i[BASE_MCCU_LIMITS:END_MCCU_LIMITS]),//One register per core
        .update_quota_i         (MCCU_update_quota_int),//Software map
        .quota_o                (regs_o[BASE_MCCU_QUOTA:END_MCCU_QUOTA]),//write back to a read register
        .events_weights_i       (MCCU_events_weights_int),//core_events times WEIGHTS_WIDTH registers
        .interruption_quota_o   (MCCU_intr_up)//N_CORES output signals Add this to top or single toplevel interrupt and an interrupt vector that identifies the source?
                                   // Individual interrupts allow each core to
                                   // handle their own interrupts , therefore
                                   //it seems to be te right solution.
    );

//----------------------------------------------
//------------- Request Duration Counter (RDC) 
//----------------------------------------------
    
    //Interruption vector to indicate signal exceeding weight
    // NON-PARAMETRIC
    wire [MCCU_N_EVENTS-1:0] interruption_rdc_o [0:MCCU_N_CORES-1];
        //core_0
    assign regs_o[BASE_RDC_VECT][1:0] = interruption_rdc_o [0] ;
        //core_1
    assign regs_o[BASE_RDC_VECT][3:2] = interruption_rdc_o [1] ;
        //core_2
    assign regs_o[BASE_RDC_VECT][5:4] = interruption_rdc_o [2] ;
        //core_3
    assign regs_o[BASE_RDC_VECT][7:6] = interruption_rdc_o [3] ;
        //spare bits on RDC_VECT
    assign regs_o[BASE_RDC_VECT][REG_WIDTH-1:8] = '{default:0} ;
    
    wire RDC_enable_int;
    assign RDC_enable_int = regs_i[BASE_MCCU_CFG][6];
    
    wire RDC_softrst;
    assign RDC_softrst = regs_i[BASE_MCCU_CFG][7];
    
    RDC #(
        // Width of data registers
        .DATA_WIDTH     (REG_WIDTH),
        // Width of weights registers
        .WEIGHTS_WIDTH  (RDC_WEIGHTS_WIDTH),
        //Cores. 
        .N_CORES        (RDC_N_CORES),
        //Signals per core. 
        .CORE_EVENTS    (RDC_N_EVENTS)
    ) inst_RDC(
        .clk_i                  (clk_i),
        .rstn_i                 (rstn_i || RDC_softrst ),
        .enable_i               (RDC_enable_int),// Software map
        .events_i               (MCCU_events_int),
        .events_weights_i       (MCCU_events_weights_int),
        // interruption signaling a signal has exceed the expected maximum request time
        .interruption_rdc_o(intr_RDC_o),
        // vector with offending signals. One hot encoding. Cleared when MCCU is disabled.
        .interruption_vector_rdc_o(interruption_rdc_o)
    );
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
    
    default clocking @(posedge clk_i); endclocking   
    // Cover that all the bits in the mask are driven
    cover property ((overflow_intr_mask_i[0]==32'b111111111) && f_past_valid );
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip


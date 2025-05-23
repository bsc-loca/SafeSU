//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Integrate PMU features under one module
// Description: Interface agnostic implementation of the  PMU. Values of the
//              PMU are not registered in this module.
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
		parameter integer REG_WIDTH	  = 32,
		// Amount of counters
		parameter integer N_COUNTERS  = 9,
		// Amount of SoC events going through the crossbar
		parameter integer N_SOC_EV	  = 32,
        // Number of cores with MCCU capabilities 
        parameter integer MCCU_N_CORES = 4, // By cf move the location   
		// Configuration registers
		parameter integer N_CONF_REGS = 1,                  
        // Width of the assigned weights for each event
        parameter integer MCCU_WEIGHTS_WIDTH = 8, // By fchang, should be parameter      
        // Number of events per core
        parameter integer MCCU_N_EVENTS = 2 ,  // By fchang, should be parameter            
        // Fault tolerance mechanisms (FT==0 -> FT disabled)
        parameter integer FT          = 0,                                           

        //------------- Internal Parameters 
		
        // *** Active functions and global configuration
        //---- Overflow
		localparam integer OVERFLOW	= 1, //Yes/No
		//---- Quota
		localparam integer QUOTA	= 1, //Yes/No
		//---- MCCU - Maximum-contention Control Unit mode
		localparam integer MCCU	    = 1, //Yes/No
		//---- RDC - Request Duration Counters
		localparam integer RDC	    = 1, //Yes/No
		//---- Crossbar
		localparam integer CROSSBAR	= 1, //Yes/No
       
        // *** Memory map related features
        
        //---- Main configuration registers
        localparam BASE_CFG = 0                        ,
        localparam END_CFG  = BASE_CFG + N_CONF_REGS -1,
        
        //---- Counter registers
        localparam BASE_COUNTERS = END_CFG + 1                 ,
        localparam END_COUNTERS  = BASE_COUNTERS + N_COUNTERS-1, 
        
        //---- Overflow interruption  registers
            // General parameters feature  
        localparam BASE_OVERFLOW_INTR = END_COUNTERS + 1,
        // mask feature
            // OVERFLOW_INTR_MASK_REGS is equivalent to $ceil(N_COUNTERS/REG_WIDTH)
        localparam BASE_OVERFLOW_MASK   = BASE_OVERFLOW_INTR                          ,
        localparam N_OVERFLOW_MASK_REGS = ((N_COUNTERS-1)/REG_WIDTH+1)                , 
        localparam END_OVERFLOW_MASK    = BASE_OVERFLOW_MASK + N_OVERFLOW_MASK_REGS -1,
        // overflow interruption vector feature
            // OVERFLOW_INTR_VECT_REGS is equivalent to $ceil(N_COUNTERS/REG_WIDTH)
        localparam BASE_OVERFLOW_VECT   = (END_OVERFLOW_MASK+1)                       ,
        localparam N_OVERFLOW_VECT_REGS = ((N_COUNTERS-1)/REG_WIDTH+1)                , 
        localparam END_OVERFLOW_VECT    = BASE_OVERFLOW_VECT + N_OVERFLOW_VECT_REGS -1,
            // General parameters overflow feature  
        localparam N_OVERFLOW_REGS   = (N_OVERFLOW_VECT_REGS + N_OVERFLOW_VECT_REGS) * OVERFLOW,
        localparam END_OVERFLOW_INTR = BASE_OVERFLOW_INTR + N_OVERFLOW_REGS -1                 ,
        
        //---- Quota interruption  registers
            // General parameters feature  
        localparam BASE_QUOTA_INTR = END_OVERFLOW_INTR + 1,
        // mask feature
            // QUOTA_INTR_MASK_REGS equivalentto to $ceil(N_COUNTERS/REG_WIDTH)
        localparam BASE_QUOTA_MASK   = BASE_QUOTA_INTR                       ,
        localparam N_QUOTA_MASK_REGS = ((N_COUNTERS-1)/REG_WIDTH+1)          , 
        localparam END_QUOTA_MASK    = BASE_QUOTA_MASK + N_QUOTA_MASK_REGS -1,
        // Available quota aka quota limit
        localparam BASE_QUOTA_LIMIT   = END_QUOTA_MASK + 1                      , 
        localparam N_QUOTA_LIMIT_REGS = 1                                       ,
        localparam END_QUOTA_LIMIT    = BASE_QUOTA_LIMIT + N_QUOTA_LIMIT_REGS -1,
        // General parameters overflow feature  
        localparam N_QUOTA_REGS   = (N_QUOTA_MASK_REGS + N_QUOTA_LIMIT_REGS ) * QUOTA,
        localparam END_QUOTA_INTR = BASE_QUOTA_INTR + N_QUOTA_REGS -1                ,
        
        //---- MCCU registers and parameters
            // General parameters feature
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
            // Watermark for each one of the available events
        localparam BASE_RDC_WATERMARK = END_RDC_VECT + 1,
                // (((....)-1)/(...)+1) is equivalent to ceil
        localparam N_RDC_WATERMARK = (((MCCU_N_CORES*MCCU_N_EVENTS*MCCU_WEIGHTS_WIDTH)-1)/REG_WIDTH+1),
        localparam END_RDC_WATERMARK = BASE_RDC_WATERMARK + N_RDC_WATERMARK -1,
            // General parameters feature  
        localparam N_RDC_REGS = (N_RDC_WEIGHTS + N_RDC_VECT_REGS+N_RDC_WATERMARK) * RDC,
        //---- CROSSBAR registers and parameters.
            // General parameters feature
        localparam CROSSBAR_INPUTS  = N_SOC_EV  ,
        localparam CROSSBAR_OUTPUTS = N_COUNTERS,
        //number of bits for each configuration field
        localparam CROSSBAR_CFG_BITS = $clog2(CROSSBAR_INPUTS)                                        ,
        localparam BASE_CROSSBAR     = END_RDC_WATERMARK +1                                           ,
        localparam N_CROSSBAR_CFG    = ((CROSSBAR_OUTPUTS*CROSSBAR_CFG_BITS-1)/REG_WIDTH+1) * CROSSBAR,
        localparam END_CROSSBAR      = BASE_CROSSBAR + N_CROSSBAR_CFG - 1                             ,
        localparam N_CROSSBAR_REGS   = N_CROSSBAR_CFG                                                 ,
        
        //---- Total of registers used
        localparam integer TOTAL_NREGS = N_COUNTERS + N_CONF_REGS + N_OVERFLOW_REGS
                                        +N_QUOTA_REGS + N_MCCU_REGS + N_RDC_REGS + N_CROSSBAR_REGS
	)
	(
		// Global Clock Signal
		input  wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input  wire  rstn_i,
        // Input/output wire from registers of the wrapper to PMU_raw internal
        // registers
        input  wire [REG_WIDTH-1:0] regs_i [0:TOTAL_NREGS-1],
        output wire [REG_WIDTH-1:0] regs_o [0:TOTAL_NREGS-1],
        // Wrapper writte enable, prevents slaves to write in to registers and
        // uploads the content with external values
        input  wire wrapper_we_i,
        // Event signals
        input  wire [N_SOC_EV-1:0] events_i,
        //interruption rises when one of the counters overflows
        output wire intr_overflow_o,
        //interruption rises when overall events quota is exceeded 
        output wire intr_quota_o,
        // MCCU interruption for exceeded quota. One signal per core
        output wire [MCCU_N_CORES-1:0] intr_MCCU_o,
        // RDC (Request Duration Counter) interruption for exceeded quota
        output wire intr_RDC_o,
        // FT (Fault tolerance) interrupt, error detected and recovered
        output wire intr_FT1_o,
        // FT (Fault tolerance) interrupt, error detected but not recoverable
        output wire intr_FT2_o,
        // Enables hardware_quota over software_quota interruptions
        output wire en_hwquota_o
	);
    //----------------------------------------------
    // VIVADO: list of debug signals for ILA 
    //----------------------------------------------     
    `ifdef ILA_DEBUG_PMU_RAW                                                           
    (* MARK_DEBUG = "TRUE" *) logic [REG_WIDTH-1:0]    debug_regs_i [0:TOTAL_NREGS-1];
    (* MARK_DEBUG = "TRUE" *) logic [REG_WIDTH-1:0]    debug_regs_o [0:TOTAL_NREGS-1]; 
    (* MARK_DEBUG = "TRUE" *) wire                     debug_wrapper_we_i            ;              
    (* MARK_DEBUG = "TRUE" *) wire  [N_SOC_EV-1:0]     debug_events_i                ;                 
    (* MARK_DEBUG = "TRUE" *) wire                     debug_intr_overflow_o         ;                 
    (* MARK_DEBUG = "TRUE" *) wire                     debug_intr_quota_o            ;                           
    (* MARK_DEBUG = "TRUE" *) wire  [MCCU_N_CORES-1:0] debug_intr_MCCU_o             ;            
    (* MARK_DEBUG = "TRUE" *) wire                     debug_intr_RDC_o              ;            
                                                                                    
    assign debug_regs_i          = regs_i         ;                                                   
    assign debug_regs_o          = regs_o         ;                                                   
    assign debug_wrapper_we_i    = wrapper_we_i   ;                                       
    assign debug_events_i        = events_i       ;                                               
    assign debug_intr_overflow_o = intr_overflow_o;                                 
    assign debug_intr_quota_o    = intr_quota_o   ;                                       
    assign debug_intr_MCCU_o     = intr_MCCU_o    ;                                         
    assign debug_intr_RDC_o      = intr_RDC_o     ;                                           
    `endif                                                                          
      
//----------------------------------------------
//------------- Declare wires from/to  wrapper registers
//----------------------------------------------
    
    //---- configuration signals
    wire [1:0]                    selftest_mode     ;
    wire                          en_i              ;
    wire                          softrst_i         ;
    wire                          overflow_en_i     ;
    wire                          overflow_softrst_i;
    wire                          quota_softrst_i   ;
    //---- Counter signals
    wire [REG_WIDTH-1:0]          counter_regs_o       [0 : N_COUNTERS-1];
    wire [REG_WIDTH-1:0]          counter_regs_int     [0 : N_COUNTERS-1];
    //---- Overflow interruption  signals
    wire [N_COUNTERS-1:0]         overflow_intr_mask_i [0 : N_OVERFLOW_MASK_REGS-1]; 
    wire [N_COUNTERS-1:0]         overflow_intr_vect_o [0 : N_OVERFLOW_VECT_REGS-1];
    //---- RDC watermark signals
    wire [MCCU_WEIGHTS_WIDTH-1:0] MCCU_watermark_int   [0:MCCU_N_CORES-1]
                                                       [0:MCCU_N_EVENTS-1];
//----------------------------------------------
//------------- Map registers from wrapper to slave functions
//----------------------------------------------
    //Selftest mode. Bypass events and sets internal values
    assign selftest_mode [0]  = regs_i [BASE_CFG][30]; 
    assign selftest_mode [1]  = regs_i [BASE_CFG][31]; 

    //counters
    assign en_i               = regs_i [BASE_CFG][0];
    assign softrst_i          = regs_i [BASE_CFG][1];
    //overflow
    assign overflow_en_i      = regs_i [BASE_CFG][2];
    assign overflow_softrst_i = regs_i [BASE_CFG][3];
    //quota    
    assign quota_softrst_i    = regs_i [BASE_CFG][4];


    // Register never set by PMU, only written by master
    genvar y;
    generate
        for(y = BASE_CFG; y <= END_CFG; y++) begin
               assign regs_o[y] = regs_i[y];
        end
    endgenerate
    //---- Counter registers
    genvar x;
    generate
        for(x = BASE_COUNTERS; x <= END_COUNTERS; x++) begin
            assign counter_regs_int[x-BASE_COUNTERS] = regs_i[x]                      ;
            assign regs_o[x]                         = counter_regs_o[x-BASE_COUNTERS];
        end
    endgenerate
    //---- Overflow interruption  registers
    generate
        for(x = 0; x < N_OVERFLOW_MASK_REGS; x++) begin
            assign overflow_intr_mask_i[x] = (rstn_i == 1'b0)? {N_COUNTERS{1'b0}} :regs_i [x+BASE_OVERFLOW_MASK][N_COUNTERS-1:0];
        end
        for(x = BASE_OVERFLOW_VECT; x <= END_OVERFLOW_VECT; x++) begin
            assign regs_o [x] = (rstn_i == 1'b0)? {REG_WIDTH{1'b0}} : REG_WIDTH'(overflow_intr_vect_o[x-BASE_OVERFLOW_VECT]);
        end
    endgenerate
        // Register never set by PMU, only written by master
    generate
        for(x = 0; x < N_OVERFLOW_MASK_REGS; x++) begin
            assign regs_o[BASE_OVERFLOW_MASK+x] = regs_i[BASE_OVERFLOW_MASK+x];
        end
    endgenerate
    //---- Quota interruption  registers
        // Register never set by PMU, only written by master
    generate
        for(x = 0; x < N_QUOTA_MASK_REGS; x++) begin
            assign regs_o[BASE_QUOTA_MASK+x] = regs_i[BASE_QUOTA_MASK+x];
        end
    endgenerate
    generate
        for(x = 0; x < N_QUOTA_LIMIT_REGS; x++) begin
            assign regs_o[BASE_QUOTA_LIMIT+x] = regs_i[BASE_QUOTA_LIMIT+x];
        end
    endgenerate
    //---- MCCU  registers
        // Register never set by PMU, only written by master
    generate
        for(x = 0; x < N_MCCU_CFG; x++) begin
            assign regs_o[BASE_MCCU_CFG+x] = regs_i[BASE_MCCU_CFG+x];
        end
    endgenerate
    generate
        for(x = 0; x < N_MCCU_LIMITS; x++) begin
            assign regs_o[BASE_MCCU_LIMITS+x] = regs_i[BASE_MCCU_LIMITS+x];
        end
    endgenerate
    generate
        for(x = 0; x < N_MCCU_WEIGHTS; x++) begin
            assign regs_o[BASE_MCCU_WEIGHTS+x] = regs_i[BASE_MCCU_WEIGHTS+x];
        end
    endgenerate
    //---- Request Duration Counter (RDC) registers 
    genvar q;
    genvar j;
    generate
        for (q = 0; q < N_MCCU_WEIGHTS; q++) begin
            for (j = 0; j < (REG_WIDTH/MCCU_WEIGHTS_WIDTH); j++) begin
                // q - Iterate over registers that we have to fill
                // j - Iterate over fields of each register
                // assign regs_o [c][d:e] =  MCCU_watermark_int[a][b];
                // a - Index of the core owning the signal
                // b - Index of the signal within the asigned core
                // c - Index of the signal in the PMU register bank
                // d - Upper bit of the field within PMU register bank
                // d - Lower bit of the field within PMU register bank
                assign regs_o[BASE_RDC_WATERMARK+q][MCCU_WEIGHTS_WIDTH*(j+1)-1:MCCU_WEIGHTS_WIDTH*j]
                        = MCCU_watermark_int [(q*(REG_WIDTH/MCCU_WEIGHTS_WIDTH)+j)/RDC_N_EVENTS]
                            [((q*(REG_WIDTH/MCCU_WEIGHTS_WIDTH)+j))%RDC_N_EVENTS];
            end
        end
    endgenerate

//----------------------------------------------
//------------- Crossbar 
//----------------------------------------------
    logic [CROSSBAR_CFG_BITS-1:0]        crossbar_cfg [0:CROSSBAR_OUTPUTS-1]; 
    logic [CROSSBAR_OUTPUTS-1:0]         crossbar_o                         ;
    logic [N_CROSSBAR_CFG*REG_WIDTH-1:0] concat_cfg_crossbar                ;

    //Drive outputs that are never set by the PMU    
    generate
        for(y = BASE_CROSSBAR; y <= END_CROSSBAR; y++) begin
            assign regs_o[y] = regs_i[y];
        end
    endgenerate

    //Concatenate all the registers to have easier access with missaligned registers 
    integer i;
    always_comb begin
        for(i = 0; i < N_CROSSBAR_CFG; i++) begin
           concat_cfg_crossbar[i*REG_WIDTH+:REG_WIDTH] = regs_i[BASE_CROSSBAR+i]; 
        end
    end

    //map configuration fields to each mux
    generate
        for(q = 0; q < CROSSBAR_OUTPUTS; q++) begin
            assign crossbar_cfg[q] = concat_cfg_crossbar [q*CROSSBAR_CFG_BITS+:CROSSBAR_CFG_BITS];
        end
    endgenerate

    //Unpack crossbar inputs
    logic unpacked_cbi_int[0:CROSSBAR_INPUTS-1];

    generate
        for(q = 0;q < CROSSBAR_INPUTS; q++) begin
            assign unpacked_cbi_int[q] = events_i[q];
        end
    endgenerate
    //Pack crossbar output
    logic unpacked_cbo_int [0:CROSSBAR_OUTPUTS-1] ;
    generate
        for(q = 0; q < CROSSBAR_OUTPUTS; q++) begin
            assign crossbar_o[q] = unpacked_cbo_int[q];
        end
    endgenerate

    //Crossbar instance
    crossbar # 
    (
    	.N_OUT	(CROSSBAR_OUTPUTS),
    	.N_IN	(CROSSBAR_INPUTS)
    )
    inst_cross   
    (
    	.clk_i    (clk_i           ),
    	.rstn_i   (rstn_i          ),
        .vector_i (unpacked_cbi_int),
        .vector_o (unpacked_cbo_int),
        .cfg_i    (crossbar_cfg    )
    );
//----------------------------------------------
//------------- Selftest configuration
//----------------------------------------------
    logic [N_COUNTERS-1:0] events_int;

    localparam NO_SELF_TEST = 2'b00;
    localparam ALL_ACTIVE   = 2'b01;
    localparam ALL_OFF      = 2'b10;
    localparam ONE_ON       = 2'b11;

    always_comb begin
        case (selftest_mode)
            NO_SELF_TEST : begin
                events_int = crossbar_o;
            end
            ALL_ACTIVE : begin
                events_int = {N_COUNTERS{1'b1}};
            end
            ALL_OFF : begin
                events_int = {N_COUNTERS{1'b0}};
            end
            ONE_ON : begin
                events_int[0]              = 1'b1;
                events_int[N_COUNTERS-1:1] = {(N_COUNTERS-1){1'b0}};
            end
        endcase
    end

//----------------------------------------------
//------------- Counters instance
//----------------------------------------------
    //TODO: What happen if we is active but no write is done to the range of the
    //counters?
    logic counters_fte2;
    PMU_counters # 
    (
    	.REG_WIDTH	(REG_WIDTH ),
    	.N_COUNTERS	(N_COUNTERS)
    )
    inst_counters 
    (
    	.clk_i      (clk_i           ),
    	.rstn_i     (rstn_i          ),
    	.softrst_i  (softrst_i       ),
    	.en_i       (en_i            ),
    	.we_i       (wrapper_we_i    ),
        .regs_i     (counter_regs_int),
        .regs_o     (counter_regs_o  ),
        .events_i   (events_int      ), 
        .intr_FT2_o (counters_fte2   )
    );

//----------------------------------------------
//------------- Overflow interuption instance
//----------------------------------------------
    PMU_overflow # 
    (
    	.REG_WIDTH	(REG_WIDTH ),
    	.N_COUNTERS	(N_COUNTERS)
    )
    inst_overflow (
    	.clk_i              (clk_i)                                 ,
    	.rstn_i             (rstn_i                                 ),
    	.softrst_i          (overflow_softrst_i                     ),
    	.en_i               (overflow_en_i                          ),
        .counter_regs_i     (counter_regs_o                         ),
        .over_intr_mask_i   (overflow_intr_mask_i[0][N_COUNTERS-1:0]), 
        .intr_overflow_o    (intr_overflow_o                        ), 
        .over_intr_vect_o   (overflow_intr_vect_o[0][N_COUNTERS-1:0])
    );

//----------------------------------------------
//------------- Quota interruption instance
//----------------------------------------------
    
    PMU_quota # 
    (
        .REG_WIDTH	(REG_WIDTH ),
        .N_COUNTERS	(N_COUNTERS)
    )
    inst_quota(
        .clk_i          (clk_i                                  ),
        .rstn_i         (rstn_i                                 ),
        .counter_value_i(counter_regs_o                         ),
        .softrst_i      (quota_softrst_i                        ),
        .quota_limit_i  (regs_i[BASE_QUOTA_LIMIT]               ),
        .quota_mask_i   (regs_i[BASE_QUOTA_MASK][N_COUNTERS-1:0]), 
        .intr_quota_o   (intr_quota_o                           ) 
    );

//----------------------------------------------
//------------- MCCU instance
//----------------------------------------------
    /*wire MCCU_enable_int;
    assign MCCU_enable_int = regs_i[BASE_MCCU_CFG][0];*/

    wire MCCU_softrst;
    assign MCCU_softrst = regs_i[BASE_MCCU_CFG][1];
        
    //hardware quota
    assign en_hwquota_o     = regs_i[BASE_MCCU_CFG][31];


    //One bit for each core to trigger quota update
    wire MCCU_update_quota_int [0:MCCU_N_CORES-1];
    generate
        for(q = 0; q < MCCU_N_CORES; q++) begin
            assign MCCU_update_quota_int[q] = regs_i[BASE_MCCU_CFG][q+2]; 
        end
    endgenerate

    //TODO: document MCCU capable events for each core configuration
        //2Cores -> events 0 to 3
        //3Cores -> events 0 to 5
        //4Cores -> events 0 to 7
        //5Cores -> events 0 to 9
        //6Cores -> events 0 to 11
    wire [MCCU_N_EVENTS-1:0] MCCU_events_int[0:MCCU_N_CORES-1];
    generate
        for(q = 0;q < MCCU_N_CORES; q++) begin
            assign MCCU_events_int [q] = {{events_int[2*q+1]},{events_int[q*2]}};
        end
    endgenerate

    wire [MCCU_WEIGHTS_WIDTH-1:0] MCCU_events_weights_int [0:MCCU_N_CORES-1]
                                                          [0:MCCU_N_EVENTS-1];
    generate
        // Registers
        for(q = 0; q < N_MCCU_WEIGHTS; q++) begin
            //fields
            for(j = 0; j < (REG_WIDTH/MCCU_WEIGHTS_WIDTH); j++) begin
                // q - Iterate over registers that we have to fill
                // j - Iterate over fields of each register
                // assign MCCU_events_weights_int [a][b] =  regs_i[c][d:e];
                // a - Index of the core owning the signal
                // b - Index of the signal within the asigned core
                // c - Index of the signal in the PMU register bank
                // d - Upper bit of the field within PMU register bank
                // d - Lowe bit of the field within PMU register bank
                assign MCCU_events_weights_int [(q*(REG_WIDTH/MCCU_WEIGHTS_WIDTH)+j)/MCCU_N_EVENTS]
                                                [((q*(REG_WIDTH/MCCU_WEIGHTS_WIDTH)+j))%MCCU_N_EVENTS] 
                        =  regs_i[BASE_MCCU_WEIGHTS+q][MCCU_WEIGHTS_WIDTH*(j+1)-1:MCCU_WEIGHTS_WIDTH*j];
            end
        end
    endgenerate
    //unpack to pack
    wire MCCU_intr_up [MCCU_N_CORES-1:0];
    generate
        case (MCCU_N_CORES)
            2 : begin
                assign intr_MCCU_o = {{MCCU_intr_up[1]},{MCCU_intr_up[0]}};
            end
            3 : begin
                assign intr_MCCU_o = {{MCCU_intr_up[2]}
                                    ,{MCCU_intr_up[1]},{MCCU_intr_up[0]}};
            end
            4 : begin
                assign intr_MCCU_o = {{MCCU_intr_up[3]},{MCCU_intr_up[2]}
                                    ,{MCCU_intr_up[1]},{MCCU_intr_up[0]}};
            end
            5 : begin
                assign intr_MCCU_o = {{MCCU_intr_up[4]}
                                    ,{MCCU_intr_up[3]},{MCCU_intr_up[2]}
                                    ,{MCCU_intr_up[1]},{MCCU_intr_up[0]}};
            end
            6 : begin
                assign intr_MCCU_o = {{MCCU_intr_up[5]},{MCCU_intr_up[4]}
                                    ,{MCCU_intr_up[3]},{MCCU_intr_up[2]}
                                    ,{MCCU_intr_up[1]},{MCCU_intr_up[0]}};
            end
            default : begin
                assign intr_MCCU_o = '{default:1};
                $error("Core configuration not supported by MCCU");
            end
        endcase
    endgenerate
    //register enable to solve Hazards
    reg MCCU_enable_int;
    always @(posedge clk_i) begin: MCCU_glitchless_enable
        if(!rstn_i) begin
            MCCU_enable_int <= 0;
        end else begin
            MCCU_enable_int <= regs_i[BASE_MCCU_CFG][0];
        end
    end
    logic MCCU_intr_FT1, MCCU_intr_FT2; 
    MCCU # 
    (
        // Width of data registers
        .DATA_WIDTH    (REG_WIDTH         ),
        // Width of weights registers
        .WEIGHTS_WIDTH (MCCU_WEIGHTS_WIDTH),
        //Cores. Change this may break Verilator TB
        .N_CORES       (MCCU_N_CORES      ),
        // Fault tolerance mechanisms (FT==0 -> FT disabled)
        .FT            (FT                ),
        //Signals per core. Change this may break Verilator TB
        .CORE_EVENTS   (MCCU_N_EVENTS     )
    )
    inst_MCCU
    (
        .clk_i                  (clk_i                                   ),
        .rstn_i                 (rstn_i && !MCCU_softrst                 ),//active low
        .enable_i               (MCCU_enable_int                         ),// Software map
        .events_i               (MCCU_events_int                         ),
        .quota_i                (regs_i[BASE_MCCU_LIMITS:END_MCCU_LIMITS]),//One register per core
        .update_quota_i         (MCCU_update_quota_int                   ),//Software map
        .quota_o                (regs_o[BASE_MCCU_QUOTA:END_MCCU_QUOTA]  ),//write back to a read register
        .events_weights_i       (MCCU_events_weights_int                 ),//core_events times WEIGHTS_WIDTH registers
        .intr_FT1_o             (MCCU_intr_FT1                           ),
        .intr_FT2_o             (MCCU_intr_FT2                           ),
        .interruption_quota_o   (MCCU_intr_up                            )//N_CORES output signals Add this to top or single toplevel interrupt and an interrupt vector that identifies the source?
                                                                          // Individual interrupts allow each core to
                                                                          // handle their own interrupts , therefore
                                                                          //it seems to be te right solution.
    );
//----------------------------------------------
//------------- Request Duration Counter (RDC) 
//----------------------------------------------
    
    //Interruption vector to indicate signal exceeding weight
    wire [MCCU_N_EVENTS-1:0] interruption_rdc_o [0:MCCU_N_CORES-1];
    generate
        for(q = 0; q < MCCU_N_CORES; q++) begin
            assign regs_o[BASE_RDC_VECT][2*q+1:q*2] = interruption_rdc_o [q] ;
        end
        //spare bits on RDC_VECT
        assign regs_o[BASE_RDC_VECT][REG_WIDTH-1:MCCU_N_CORES*2] = '{default:0} ;
    endgenerate

    if(FT == 0) begin
    //register enable to solve Hazards
        // Does not nid replication since regs_i is already protected
        // RDC_enable_int may be disabled for a single cycle but
        // it will not be a permanent fault
    reg RDC_enable_int;
    always @(posedge clk_i) begin: RDC_glitchless_enable
        if(!rstn_i) begin
            RDC_enable_int <= 0;
        end else begin
            // Offset MCCU soft rest, enable and individual core updates
            RDC_enable_int <= regs_i[BASE_MCCU_CFG][MCCU_N_CORES+2];
        end
    end 
    RDC #
    (
        // Width of data registers
        .DATA_WIDTH    (REG_WIDTH        ),
        // Width of weights registers
        .WEIGHTS_WIDTH (RDC_WEIGHTS_WIDTH),
        //Cores. 
        .N_CORES       (RDC_N_CORES      ),
        //Signals per core. 
        .CORE_EVENTS   (RDC_N_EVENTS     )
    ) 
    inst_RDC
    (
        .clk_i                     (clk_i                              ),
        .rstn_i                    (rstn_i && !regs_i[BASE_MCCU_CFG][MCCU_N_CORES+3]), //active low
        .enable_i                  (RDC_enable_int                     ),// Software map
        .events_i                  (MCCU_events_int                    ),
        .events_weights_i          (MCCU_events_weights_int            ),
        // interruption signaling a signal has exceed the expected maximum request time
        .interruption_rdc_o        (intr_RDC_o                         ),
        // vector with offending signals. One hot encoding. Cleared when MCCU is disabled.
        .interruption_vector_rdc_o (interruption_rdc_o                 ),
        //maximum pulse length of a given core event
        .watermark_o               (MCCU_watermark_int                 ) 
    );
    end else begin : Rdctrip
    //register enable to solve Hazards
        // Does not nid replication since regs_i is already protected
        // RDC_enable_int may be disabled for a single cycle but
        // it will not be a permanent fault
    logic RDC_enable_int_D, RDC_enable_int_Q;
    logic RDC_enable_fte1, RDC_enable_fte2;
    triple_reg #
    (
        .IN_WIDTH (1)
    )
    RDC_enable_trip
    (
        .clk_i    (clk_i           ),
        .rstn_i   (rstn_i          ),
        .din_i    (RDC_enable_int_D),
        .dout_o   (RDC_enable_int_Q),
        .error1_o (RDC_enable_fte1 ), // ignore corrected errors
        .error2_o (RDC_enable_fte2 )
    );
    always_comb begin
        if(!rstn_i) begin
            RDC_enable_int_D = 0;
        end else begin
            RDC_enable_int_D = regs_i[BASE_MCCU_CFG][MCCU_N_CORES+2];
        end
    end 

    //Signals from instances to way3 voter
        //inst
    logic intr_RDC_ft0 ;
    logic [MCCU_N_EVENTS-1:0]      interruption_rdc_ft0 [0:MCCU_N_CORES-1];
    logic [MCCU_WEIGHTS_WIDTH-1:0] MCCU_watermark_ft0   [0:MCCU_N_CORES-1]
                                                        [0:MCCU_N_EVENTS-1];
        //inst1
    logic intr_RDC_ft1 ;
    logic [MCCU_N_EVENTS-1:0]      interruption_rdc_ft1 [0:MCCU_N_CORES-1];
    logic [MCCU_WEIGHTS_WIDTH-1:0] MCCU_watermark_ft1   [0:MCCU_N_CORES-1]
                                                        [0:MCCU_N_EVENTS-1];
        //inst2
    logic intr_RDC_ft2 ;
    logic [MCCU_N_EVENTS-1:0]      interruption_rdc_ft2 [0:MCCU_N_CORES-1];
    logic [MCCU_WEIGHTS_WIDTH-1:0] MCCU_watermark_ft2   [0:MCCU_N_CORES-1]
                                                        [0:MCCU_N_EVENTS-1];
    //FT error detected signals
    //Even when the error is corrected latent faults may be present on this signals
        // and software shall clear them
    logic intr_RDC_fte1, interruption_rdc_fte1, MCCU_watermark_fte1; 
    logic intr_RDC_fte2, interruption_rdc_fte2, MCCU_watermark_fte2;
    RDC #
    (
        .DATA_WIDTH    (REG_WIDTH        ),
        .WEIGHTS_WIDTH (RDC_WEIGHTS_WIDTH),
        .N_CORES       (RDC_N_CORES      ),
        .CORE_EVENTS   (RDC_N_EVENTS     )
    ) 
    inst_RDC
    (
        .clk_i                     (clk_i                              ),
        .rstn_i                    (rstn_i && !regs_i[BASE_MCCU_CFG][MCCU_N_CORES+3]), //active low
        .enable_i                  (RDC_enable_int_Q                   ),// Software map
        .events_i                  (MCCU_events_int                    ),
        .events_weights_i          (MCCU_events_weights_int            ),
        .interruption_rdc_o        (intr_RDC_ft0                       ),
        .interruption_vector_rdc_o (interruption_rdc_ft0               ),
        .watermark_o               (MCCU_watermark_ft0                 ) 
    );
    RDC #
    (
        .DATA_WIDTH    (REG_WIDTH),
        .WEIGHTS_WIDTH (RDC_WEIGHTS_WIDTH),
        .N_CORES       (RDC_N_CORES),
        .CORE_EVENTS   (RDC_N_EVENTS)
    ) 
    inst1_RDC
    (
        .clk_i                     (clk_i                              ),
        .rstn_i                    (rstn_i && !regs_i[BASE_MCCU_CFG][MCCU_N_CORES+3]), //active low
        .enable_i                  (RDC_enable_int_Q                   ),// Software map
        .events_i                  (MCCU_events_int                    ),
        .events_weights_i          (MCCU_events_weights_int            ),
        .interruption_rdc_o        (intr_RDC_ft1                       ),
        .interruption_vector_rdc_o (interruption_rdc_ft1               ),
        .watermark_o               (MCCU_watermark_ft1                 ) 
    );
    RDC #
    (
        .DATA_WIDTH    (REG_WIDTH),
        .WEIGHTS_WIDTH (RDC_WEIGHTS_WIDTH),
        .N_CORES       (RDC_N_CORES),
        .CORE_EVENTS   (RDC_N_EVENTS)
    ) 
    inst2_RDC
    (
        .clk_i                     (clk_i                              ),
        .rstn_i                    (rstn_i && !regs_i[BASE_MCCU_CFG][MCCU_N_CORES+3]), //active low
        .enable_i                  (RDC_enable_int_Q                   ),// Software map
        .events_i                  (MCCU_events_int                    ),
        .events_weights_i          (MCCU_events_weights_int            ),
        .interruption_rdc_o        (intr_RDC_ft2                       ),
        .interruption_vector_rdc_o (interruption_rdc_ft2               ),
        .watermark_o               (MCCU_watermark_ft2                 ) 
    );
    // intr_RDC_ft
    way3_voter #
    (
    	.IN_WIDTH (1)
    )
    intr_RDC_way3
    (
        .in0      (intr_RDC_ft0 ),
        .in1      (intr_RDC_ft1 ),
        .in2      (intr_RDC_ft2 ),
        .out      (intr_RDC_o   ),
        .error1_o (intr_RDC_fte1),
        .error2_o (intr_RDC_fte2)
    );
    // interruption_rdc_ft
    way3ua_voter #
    (
    	.W (MCCU_N_EVENTS),
    	.U (MCCU_N_CORES )
    )
    interruption_rdc_way3
    (
        .in0      (interruption_rdc_ft0 ),
        .in1      (interruption_rdc_ft1 ),
        .in2      (interruption_rdc_ft2 ),
        .out      (interruption_rdc_o   ),
        .error1_o (interruption_rdc_fte1),
        .error2_o (interruption_rdc_fte2)
    );
    // MCCU_watermark_ft
    way3u2a_voter #
    (
    	.W (MCCU_WEIGHTS_WIDTH),
    	.U (MCCU_N_CORES      ),
    	.D (MCCU_N_EVENTS     )
    )
    watermark_way3
    (
        .in0     (MCCU_watermark_ft0 ),
        .in1     (MCCU_watermark_ft1 ),
        .in2     (MCCU_watermark_ft2 ),
        .out     (MCCU_watermark_int ),
        .error1_o(MCCU_watermark_fte1),
        .error2_o(MCCU_watermark_fte2)
    );
    end
//----------------------------------------------
//------------- Generate intr_FT_o
//----------------------------------------------
    if(FT == 0 ) begin
        assign intr_FT1_o = 1'b0;
        assign intr_FT2_o = 1'b0;
    end else begin 
        //Gather all the signals of corrected errors from FT scopes
            // Codestyle. All scopes start with a capital letter
        assign intr_FT1_o = |{
                            Rdctrip.MCCU_watermark_fte1,Rdctrip.intr_RDC_fte1,
                            Rdctrip.interruption_rdc_fte1,Rdctrip.RDC_enable_fte1,
                            MCCU_intr_FT1 
                             };
        //Gather all the signals of uncorrected errors from FT scopes
            // Codestyle. All scopes start with a capital letter
        assign intr_FT2_o = |{
                            Rdctrip.MCCU_watermark_fte2,Rdctrip.intr_RDC_fte2,
                            Rdctrip.interruption_rdc_fte2,Rdctrip.RDC_enable_fte2,
                            MCCU_intr_FT2, 
                        counters_fte2
                         };
    end
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
    //auxiliar registers
    reg f_past_valid ;
    initial f_past_valid = 1'b0;
    //Set f_past_valid after first clock cycle
    always @(posedge clk_i)
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


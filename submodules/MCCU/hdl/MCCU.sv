//-----------------------------------------------------
// ProjectName: PMU research 
// Function   : Implementation of Maximum-Contention Control Unit (MCCU): 
//              ResourceAccess Count and Contention Time Enforcement.
// Description: Mechanism that estimates the contention caused for each event,
//              the contention caused is substracted from the asigned quota.
//              When the quota is 0 an interrupt is risen.
// Coder      : G.Cabo
// References : https://upcommons.upc.edu/handle/2117/133656

`default_nettype none
//`define DEBUG

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif

`timescale 1 ns / 1 ps
	module MCCU #
	(
		// Width of data registers
		parameter integer DATA_WIDTH	= 32,
		// Width of weights registers
		parameter integer WEIGHTS_WIDTH	= 8,
        //Cores. Change this may break Verilator TB
        parameter integer N_CORES       =2,
        // Fault tolerance mechanisms (FT==0 -> FT disabled)
        parameter integer FT  = 0,                                           
        //Signals per core. Change this may break Verilator TB
        parameter integer CORE_EVENTS   =4
	)
	(
		input wire clk_i,
        //Active low syncronous reset. It can have hardware or software source
		input wire rstn_i,
		//Active high enable. If enabled quota can decrease and interruptions
        //can be generated
        input wire enable_i,
        //Monitored events that can generate contention in the system
        input wire [CORE_EVENTS-1:0] events_i [0:N_CORES-1],
        //Quota for each of the cores, internally registered, set by software
        input wire [DATA_WIDTH-1:0] quota_i [0:N_CORES-1],
        //Update quota. Set quota_int to the value of quota_i
        input wire update_quota_i [0:N_CORES-1],
        //Internal quota available
        output wire [DATA_WIDTH-1:0] quota_o [0:N_CORES-1],
        //Worst contention that  each of the previous events can generate,
        //internally registered, set by software, if 0 event is dissabled
        input wire [WEIGHTS_WIDTH-1:0] events_weights_i [0:N_CORES-1]
                                                       [0:CORE_EVENTS-1],
        //Quota interruption
        output wire interruption_quota_o[N_CORES-1:0],
        // FT (Fault tolerance) interrupt, error detected and recovered
        output wire intr_FT1_o,
        // FT (Fault tolerance) interrupt, error detected but not recoverable
        output wire intr_FT2_o
    );
    //Parameters required for additions and substractions of quotas.
    //OVERFLOW_PROT can be reduced. It needs to be a bit larger than 
    //DATA_WIDTH. 
    localparam integer OVERFLOW_PROT = DATA_WIDTH*2;
    //avoid width mismatch when add: OVERFLOW_PROT + DATA_WIDTH
    localparam O_D_0PAD = OVERFLOW_PROT-DATA_WIDTH;
    //avoid width mismatch when add: DATA_WIDTH + WEIGHTS_WIDTH
    localparam D_W_0PAD = DATA_WIDTH-WEIGHTS_WIDTH;
    //avoid width mismatch when add: OVERFLOW_PROT + WEIGHTS_WIDTH
    localparam O_W_0PAD = OVERFLOW_PROT-WEIGHTS_WIDTH;
    
    //internal signals
    wire [WEIGHTS_WIDTH-1:0] events_weights_int [0:N_CORES-1] [0:CORE_EVENTS-1];
    `ifdef DEBUG
    reg [OVERFLOW_PROT-1:0] debug_ccc_suma_int;//Just one core
    reg [OVERFLOW_PROT-1:0] debug_ccc_suma_loop_int;//Just one core
    reg [WEIGHTS_WIDTH-1:0] debug_events_weights_int [0:CORE_EVENTS-1];//Just one core
    integer k;  
    integer debug_tmp = 0;
    `endif
    /*----------
    Generate one mechanism to monitor the quota for each of the cores in the
    SOC,
    ----------*/
    if (FT==0) begin : Nft_suma
        // Define internal signals within generate scope
        reg [OVERFLOW_PROT-1:0] ccc_suma_int [0:N_CORES-1];//Addition of current cycle
                                                   //consumed quota
        reg [DATA_WIDTH-1:0] quota_int [0:N_CORES-1];//Quota set by external registers
        integer i;
        integer j;
    //    generate begin : GeneratedQuotaMonitor
        always @(posedge clk_i) begin: syncReset
            /*----------
            Auxiliar variables
            ----------*/
            longint tmp_ccc_suma_int;//temporal addition of ccc_suma_int
            /*----------
            Reset 
            ----------*/
            if(rstn_i == 1'b0 ) begin
                /*----------
                sync reset Quota
                ----------*/
                for (i=0; i<N_CORES; i=i+1) begin : ResetQuota
                    quota_int[i] <={DATA_WIDTH{1'b0}}; 
                end
                /*----------
                sync reset current cycle consumed quota
                ----------*/
                for (i=0; i<N_CORES; i=i+1) begin : ResetCCCQuota
                    ccc_suma_int[i] <={OVERFLOW_PROT{1'b0}}; 
                end
                /*----------
                sync reset debug registers
                ----------*/
                `ifdef DEBUG
                debug_ccc_suma_int <= {OVERFLOW_PROT{1'b0}};
                debug_ccc_suma_loop_int <= {OVERFLOW_PROT{1'b0}};
                for (i=0; i<N_CORES; i=i+1) begin : ResetDebugEvents
                debug_events_weights_int [i]<= {WEIGHTS_WIDTH{1'b0}};
                end
                `endif
            end else begin
            /*----------
            Normal operation
            ----------*/
                /*----------
                Substract to the core quota the weight of each active
                event during this cycle. If the event is active the value
                of the weight is substracted, if not 0 is substracted. Only
                substract quota if enable is active. If the quota has been updated
                this cycle  quota_i is bypass
                ----------*/
                
                //Cases to change the values of quota
                `ifdef ASSERTIONS
                //If unit was not in reset and has not been reseted this cycle
                if($past(rstn_i)&& rstn_i) begin
                    for (i=0; i<N_CORES; i=i+1) begin : AssertionsQuotaNonReset
                        //!Enable && !update: hold values quota_int
                        if(!$past(enable_i) && !$past(update_quota_i[i])) begin
                            assert(quota_int[i] == $past(quota_int[i]));
                        end
                        
                        //!Enable && update: Update values quota_int with quota_i,
                        //                      do NOT substract 
                        if(!$past(enable_i) && $past(update_quota_i[i])) begin
                            assert(quota_int[i] == $past(quota_i[i]));
                        end
                        
                        //Enable && !update:Replace quota_int with quota_int minus
                        //                      consumed quota (ccc_quota). If
                        //                      underflow the content of 
                        //                      quota_int[i] can be 0.
                        if($past(enable_i) && !$past(update_quota_i[i])) begin
                            assert(quota_int[i] == ($past(quota_int[i])-$past(ccc_suma_int[i])) 
                                                    || (quota_int[i]==
                                                       {DATA_WIDTH{1'b0}}));
                        end
                        
                        //Enable && update: Update values quota_int with quota_i and 
                        //                      substract ccc_quota if  
                        //                      underflow the content of 
                        //                      quota_int[i] can be 0.
                        if($past(enable_i) && $past(update_quota_i[i])) begin
                            assert(quota_int[i] == ($past(quota_i[i])-$past(ccc_suma_int[i]))
                                                    || (quota_int[i]==
                                                       {DATA_WIDTH{1'b0}}));
                        end
                    end
                end else begin
                //if the  unit has been reseted in current or  previous cycle
                    for (i=0; i<N_CORES; i=i+1) begin : AssertionsQuotaReset
                        assert(quota_int[i] == {DATA_WIDTH{1'b0}});
                    end
                end
                `endif

                for (i=0; i<N_CORES; i=i+1) begin : SetQuota
                    //!Enable && !update: hold values quota_int
                    if(!enable_i && !update_quota_i[i]) begin
                        quota_int[i] <= quota_int[i];
                    //!Enable && update: Update values quota_int with quota_i,
                    //                      do NOT substract 
                    end else if (!enable_i && update_quota_i[i]) begin
                        quota_int[i] <= quota_i[i]; 
                    //Enable && !update:Replace quota_int with quota_int minus
                    //                      consumed quota (ccc_quota)
                    end else if (enable_i && !update_quota_i[i]) begin
                        for (j=0; j<CORE_EVENTS; j=j+1) begin
                                //underflow detection. Padding needed for
                                // prevent width mismatch
                                if( ccc_suma_int[i] > {{O_D_0PAD{1'b0}},quota_int[i]} )
                                begin
                                    quota_int[i] <={DATA_WIDTH{1'b0}};  
                                end else begin
                                    quota_int[i] <= quota_int[i] - ccc_suma_int[i][DATA_WIDTH-1:0];  
                                end
                        end
                    //Enable && update: Update values quota_int with quota_i and 
                    //                      substract ccc_quota 
                    end else if(enable_i && update_quota_i[i])begin
                        for (j=0; j<CORE_EVENTS; j=j+1) begin
                                //underflow detection. Padding needed for
                                // prevent width mismatch
                                if( ccc_suma_int[i] > {{O_D_0PAD{1'b0}},quota_i[i]} )
                                begin
                                    quota_int[i] <={DATA_WIDTH{1'b0}};  
                                end else begin
                                    quota_int[i] <= quota_i[i] - ccc_suma_int[i][DATA_WIDTH-1:0];  
                                end
                        end
                    end
                end
                /*----------
                Add quotas of all active signals. The ones that are not
                enabled are 0. The quotas in  ccc_suma_int[i] are added at every
                cycle independently of the enable signal, but ccc_suma_int will
                only be substracted to the quota if MCCU is enabled
                ----------*/ 
                for (i=0; i<N_CORES; i=i+1) begin : AddEventsWeights
                    tmp_ccc_suma_int=0;
                    for (j=0; j<CORE_EVENTS; j=j+1) begin
                            //Reguired to avoid warning. Blocking
                            //Assigment is legal when usign temporal
                            //variables.
                            /* verilator lint_off BLKSEQ */
                            tmp_ccc_suma_int ={{O_W_0PAD{1'b0}},events_weights_int[i][j]} + tmp_ccc_suma_int;  
                            /* verilator lint_on BLKSEQ */
                    end
                    ccc_suma_int[i]<=tmp_ccc_suma_int;
                    `ifdef DEBUG
                    /* verilator lint_off WIDTH */
                    /* verilator lint_off BLKSEQ */
                    //This only applies when 4 events are available
                        if(i==0 && CORE_EVENTS==4) begin
                            debug_events_weights_int <= events_weights_int [0];//assign to core 0
                            debug_ccc_suma_int <= debug_events_weights_int[0]+debug_events_weights_int[1]+debug_events_weights_int[2]+debug_events_weights_int[3];
                            debug_tmp=0;
                            for(k=0; k<CORE_EVENTS; k=k+1) begin
                                    debug_tmp  =debug_events_weights_int[k] + debug_tmp;  
                            end
                            debug_ccc_suma_loop_int <= debug_tmp;
                        end
                        
                        `ifdef ASSERTIONS
                        assert(debug_ccc_suma_int == debug_ccc_suma_loop_int);
                        `endif
                    //disable BLKSeK for the temporal assigment of debug_tmp
                    /* verilator lint_on BLKSEQ */
                    /* verilator lint_on WIDTH */
                    `endif
                end
            end 
        end
    end else begin : Ft_suma 
        // Code for FT version
        //Triplicate registers of interest
            //Addition of current cycle consumed quota
        reg [OVERFLOW_PROT-1:0] ccc_suma_int_0 [0:N_CORES-1];
        reg [OVERFLOW_PROT-1:0] ccc_suma_int_1 [0:N_CORES-1];
        reg [OVERFLOW_PROT-1:0] ccc_suma_int_2 [0:N_CORES-1];
            //Voted ccc_suma_int
        logic [OVERFLOW_PROT-1:0] ccc_suma_vint [0:N_CORES-1];
        logic interruption_ccc_suma_fte1, interruption_ccc_suma_fte2;
            //Quota set by external registers
        reg [DATA_WIDTH-1:0] quota_int_0 [0:N_CORES-1];
        reg [DATA_WIDTH-1:0] quota_int_1 [0:N_CORES-1];
        reg [DATA_WIDTH-1:0] quota_int_2 [0:N_CORES-1];
            //Voted quota int
        logic [DATA_WIDTH-1:0] quota_vint [0:N_CORES-1];
        logic interruption_quota_fte1, interruption_quota_fte2;
        // generate loop vars
        integer i;
        integer j;
        //Generate voted outputs
        way3ua_voter #(
            .W(OVERFLOW_PROT),
            .U(N_CORES)
        )ccc_sum_way3(
            .in0(ccc_suma_int_0),
            .in1(ccc_suma_int_1),
            .in2(ccc_suma_int_2),
            .out(ccc_suma_vint),
            .error1_o(interruption_ccc_suma_fte1),
            .error2_o(interruption_ccc_suma_fte2)
        );
        way3ua_voter #(
            .W(DATA_WIDTH),
            .U(N_CORES)
        )quota_way3(
            .in0(quota_int_0),
            .in1(quota_int_1),
            .in2(quota_int_2),
            .out(quota_vint),
            .error1_o(interruption_quota_fte1),
            .error2_o(interruption_quota_fte2)
        );

        //    generate begin : GeneratedQuotaMonitor
        always @(posedge clk_i) begin: syncReset
            /*----------
            Auxiliar variables
            ----------*/
            longint tmp_ccc_suma_int;//temporal addition of ccc_suma_int
            /*----------
            Reset 
            ----------*/
            if(rstn_i == 1'b0 ) begin
                /*----------
                sync reset Quota
                ----------*/
                for (i=0; i<N_CORES; i=i+1) begin : ResetQuota
                    quota_int_0[i] <={DATA_WIDTH{1'b0}}; 
                    quota_int_1[i] <={DATA_WIDTH{1'b0}}; 
                    quota_int_2[i] <={DATA_WIDTH{1'b0}}; 
                end
                /*----------
                sync reset current cycle consumed quota
                ----------*/
                for (i=0; i<N_CORES; i=i+1) begin : ResetCCCQuota
                    ccc_suma_int_0[i] <={OVERFLOW_PROT{1'b0}}; 
                    ccc_suma_int_1[i] <={OVERFLOW_PROT{1'b0}}; 
                    ccc_suma_int_2[i] <={OVERFLOW_PROT{1'b0}}; 
                end
            end else begin
            /*----------
            Normal operation
            ----------*/
                /*----------
                Substract to the core quota the weight of each active
                event during this cycle. If the event is active the value
                of the weight is substracted, if not 0 is substracted. Only
                substract quota if enable is active. If the quota has been updated
                this cycle  quota_i is bypass
                ----------*/
                for (i=0; i<N_CORES; i=i+1) begin : SetQuota
                    //!Enable && !update: hold values quota_int
                    if(!enable_i && !update_quota_i[i]) begin
                        quota_int_0[i] <= quota_vint[i];
                        quota_int_1[i] <= quota_vint[i];
                        quota_int_2[i] <= quota_vint[i];
                    //!Enable && update: Update values quota_int with quota_i,
                    //                      do NOT substract 
                    end else if (!enable_i && update_quota_i[i]) begin
                        quota_int_0[i] <= quota_i[i]; 
                        quota_int_1[i] <= quota_i[i]; 
                        quota_int_2[i] <= quota_i[i]; 
                    //Enable && !update:Replace quota_int with quota_int minus
                    //                      consumed quota (ccc_quota)
                    end else if (enable_i && !update_quota_i[i]) begin
                        for (j=0; j<CORE_EVENTS; j=j+1) begin
                                //underflow detection. Padding needed for
                                // prevent width mismatch
                                if( ccc_suma_vint[i] > {{O_D_0PAD{1'b0}},quota_vint[i]} )
                                begin
                                    quota_int_0[i] <={DATA_WIDTH{1'b0}};  
                                    quota_int_1[i] <={DATA_WIDTH{1'b0}};  
                                    quota_int_2[i] <={DATA_WIDTH{1'b0}};  
                                end else begin
                                    quota_int_0[i] <= quota_vint[i] - ccc_suma_vint[i][DATA_WIDTH-1:0];  
                                    quota_int_1[i] <= quota_vint[i] - ccc_suma_vint[i][DATA_WIDTH-1:0];  
                                    quota_int_2[i] <= quota_vint[i] - ccc_suma_vint[i][DATA_WIDTH-1:0];  
                                end
                        end
                    //Enable && update: Update values quota_int with quota_i and 
                    //                      substract ccc_quota 
                    end else if(enable_i && update_quota_i[i])begin
                        for (j=0; j<CORE_EVENTS; j=j+1) begin
                                //underflow detection. Padding needed for
                                // prevent width mismatch
                                if( ccc_suma_vint[i] > {{O_D_0PAD{1'b0}},quota_i[i]} )
                                begin
                                    quota_int_0[i] <={DATA_WIDTH{1'b0}};  
                                    quota_int_1[i] <={DATA_WIDTH{1'b0}};  
                                    quota_int_2[i] <={DATA_WIDTH{1'b0}};  
                                end else begin
                                    quota_int_0[i] <= quota_i[i] - ccc_suma_vint[i][DATA_WIDTH-1:0];  
                                    quota_int_1[i] <= quota_i[i] - ccc_suma_vint[i][DATA_WIDTH-1:0];  
                                    quota_int_2[i] <= quota_i[i] - ccc_suma_vint[i][DATA_WIDTH-1:0];  
                                end
                        end
                    end
                end
                /*----------
                Add quotas of all active signals. The ones that are not
                enabled are 0. The quotas in  ccc_suma_int[i] are added at every
                cycle independently of the enable signal, but ccc_suma_int will
                only be substracted to the quota if MCCU is enabled
                ----------*/ 
                for (i=0; i<N_CORES; i=i+1) begin : AddEventsWeights
                    tmp_ccc_suma_int=0;
                    for (j=0; j<CORE_EVENTS; j=j+1) begin
                            //Reguired to avoid warning. Blocking
                            //Assigment is legal when usign temporal
                            //variables.
                            /* verilator lint_off BLKSEQ */
                            tmp_ccc_suma_int ={{O_W_0PAD{1'b0}},events_weights_int[i][j]} + tmp_ccc_suma_int;  
                            /* verilator lint_on BLKSEQ */
                    end
                    ccc_suma_int_0[i]<=tmp_ccc_suma_int;
                    ccc_suma_int_1[i]<=tmp_ccc_suma_int;
                    ccc_suma_int_2[i]<=tmp_ccc_suma_int;
                    `ifdef DEBUG
                    /* verilator lint_off WIDTH */
                    /* verilator lint_off BLKSEQ */
                    //This only applies when 4 events are available
                        if(i==0 && CORE_EVENTS==4) begin
                            debug_events_weights_int <= events_weights_int [0];//assign to core 0
                            debug_ccc_suma_int <= debug_events_weights_int[0]+debug_events_weights_int[1]+debug_events_weights_int[2]+debug_events_weights_int[3];
                            debug_tmp=0;
                            for(k=0; k<CORE_EVENTS; k=k+1) begin
                                    debug_tmp  =debug_events_weights_int[k] + debug_tmp;  
                            end
                            debug_ccc_suma_loop_int <= debug_tmp;
                        end
                        
                        `ifdef ASSERTIONS
                        assert(debug_ccc_suma_int == debug_ccc_suma_loop_int);
                        `endif
                    //disable BLKSeK for the temporal assigment of debug_tmp
                    /* verilator lint_on BLKSEQ */
                    /* verilator lint_on WIDTH */
                    `endif
                end
            end 
        end
    end
    /*----------
    Set weights of events, as this module is used whith a 
    wrapper the values are already registered 
    outside and only need to be forwarded without register them internally.
    Apply the event as a mask. If the event is inactive in the current cycle
    0 is forwarded in events_weights_int for that event.
    ----------*/
    genvar x;
    genvar y;
    for (x=0; x<N_CORES; x=x+1) begin : SetEventsWeights
        for (y=0; y<CORE_EVENTS; y=y+1) begin
            assign     events_weights_int [x][y] = events_i[x][y] ? events_weights_i[x][y]:{WEIGHTS_WIDTH{1'b0}};
        end
    end
    /*----------
    Generate interruptions for quota for each core. Interrupt triggers
    one cycle before the result is registered. There is no record of
    by how much the quota was exceeded. Interruption is only generated if the 
    MCCU is enabled
    ----------*/
    wire interruption_quota_d[N_CORES-1:0];
    reg interruption_quota_q[N_CORES-1:0];
    
    if (FT==0) begin
        for(x=0; x<N_CORES; x=x+1)  begin: InterruptionQuota
            assign interruption_quota_d[x] =
                     !enable_i ? 1'b0:
                     (Nft_suma.ccc_suma_int[x]>{{O_D_0PAD{1'b0}},Nft_suma.quota_int[x]})? 1'b1:1'b0;
        end
    end else begin
        for(x=0; x<N_CORES; x=x+1)  begin: InterruptionQuota
            assign interruption_quota_d[x] =
                     !enable_i ? 1'b0:
                     (Ft_suma.ccc_suma_vint[x]>{{O_D_0PAD{1'b0}},Ft_suma.quota_vint[x]})? 1'b1:1'b0;
        end
    end
    

    for(x=0; x<N_CORES; x=x+1)  begin: InterruptionQuotaHold
        always @(posedge clk_i) begin
            if(rstn_i == 1'b0 ) begin
                interruption_quota_q[x] <= 1'b0;
            end else begin
                if(enable_i) begin
                    interruption_quota_q[x] <= interruption_quota_d[x] | interruption_quota_q[x];
                end else begin
                    interruption_quota_q[x] <= 1'b0;
                end
            end
        end
        assign interruption_quota_o[x] = (enable_i && rstn_i) ? interruption_quota_q[x] : 1'b0;
    end

    `ifdef ASSERTIONS
    if(FT==0) begin
        always @(posedge clk_i) begin
            for(integer x=0; x<N_CORES; x=x+1)  begin: InterruptionQuota
                if(Nft_suma.quota_int[x]>Nft_suma.ccc_suma_int[x])
                    assert (interruption_quota_d[x]==1'b0);
            end
        end
    end
    `endif
    /*----------
    forward results of internal registers 
    ----------*/
    if (FT==0) begin
        assign quota_o = Nft_suma.quota_int;
    end else begin
        assign quota_o = Ft_suma.quota_vint;
    end

    //----------------------------------------------
    //------------- Generate intr_FT_o
    //----------------------------------------------
    if (FT == 0 ) begin
            assign intr_FT1_o = 1'b0;
            assign intr_FT2_o = 1'b0;
    end else begin 
            //Gather all the signals of corrected errors from FT scopes
                // Codestyle. All scopes start with a capital letter
            assign intr_FT1_o = |{
                                    Ft_suma.interruption_ccc_suma_fte1,
                                    Ft_suma.interruption_quota_fte1
                                 };
            //Gather all the signals of uncorrected errors from FT scopes
                // Codestyle. All scopes start with a capital letter
            assign intr_FT2_o = |{
                                    Ft_suma.interruption_ccc_suma_fte2,
                                    Ft_suma.interruption_quota_fte2
                                 };
    end
/*----------
Section of Formal propperties, valid for SBY 
----------*/
`ifdef	FORMAL
    //auxiliar registers
    reg f_past_valid ;
    initial f_past_valid = 1'b0;
    longint f_sum_weights;
    //Set f_past_valid after first clock cycle
    always@( posedge clk_i )
        f_past_valid <= 1'b1;
   
    //assume that if f_past is not valid you have to reset
    //TODO: Will this lead to problems with k-insuction?
    always @(*) begin
		if(0 == f_past_valid) begin
            assume(0 == rstn_i);
         end
    end
    /*--------------
      When reset (rstn_i)is active all internal registers shall be set to 0 in 
      the next cycle.
    --------------*/
    if(FT==0) begin
    always @(posedge clk_i) begin
		if(0 == $past(rstn_i) && f_past_valid) begin
            assert(0 == Nft_suma.quota_int.sum()); 
            assert(0 == Nft_suma.ccc_suma_int.sum()); 
        end
    end
    end
    /*--------------
      Unless a reset occures, the addition of all current cycle consumed
      quota by all the cores (ccc_suma_int[i]) shall be the same that the 
      addition of all the internal weights (events_weights_int[i][j]) of the 
      previous cycle. Internal weights are non registerd and they set to 0 if 
      the signal for a given weight is not active the current cycle.
    --------------*/  
    //Auxiliar logic to compute sum of all signals and consumed quota
    int i , j; 
    always@( posedge clk_i) begin
        f_sum_weights =0; //initialize to 0 and add events_weights_int
        if(rstn_i) begin // reset disabled
                for (i=0; i<N_CORES; i=i+1) begin
                    for (j=0; j<CORE_EVENTS; j=j+1) begin
                        f_sum_weights=f_sum_weights + events_weights_int[i][j];
                    end
                end
        end
    end
    //assert that the addition of quotas consumed in the current cycle
    //equal to the internal weights.
    if(FT==0) begin
        always @(posedge clk_i) begin
            if(rstn_i) begin
                assert(f_sum_weights == Nft_suma.ccc_suma_int.sum());
            end 
        end
    end
    /*---------
     * checks when the interruption can be triggered
     * --------*/
    //Interruption can be only high if consumed quota is larger than
    //available quota and the MCCU is enabled

    default clocking @(posedge clk_i); endclocking;
    
    genvar k;
    for(k=0;k<N_CORES;k++) begin
    // If the unit is in reset or disabled the interrupts shall be 0 immediately.
    assert property (
                    (f_past_valid && (rstn_i==0 || enable_i==0))
                    |->
                    (!interruption_quota_o[k])
                    );
    // If an interrup is actrive it shall remain high unless there is a reset
    assert property (
                    (f_past_valid && (interruption_quota_o[k]==1'b1))
                    |=>
                    ($stable(interruption_quota_o[k]) || (!rstn_i || !enable_i))
                    );

    /// If unit is not in reset or disabled. When quota_int[k]<ccc_suma_int[k] the interrupt 
        //shall rise in the next cycle

    end 
/*
    always @(posedge clk_i) begin
        for(k=0;k<N_CORES;k++) begin
            if (f_past_valid && rstn_i) begin
                if (($past(quota_int[k]<ccc_suma_int[k]) && enable_i)) begin
                    //The interruption shall be high
                    assert(interruption_quota_[k]==1'b1);
                    //The interruption can only be high if the MCCU is enabled
                    assert(interruption_quota_o[k]==enable_i);
                end else begin
                    //interruption shall be disabled if not enabled or unit in reset
                    if (enable_i== 0 || rstn_i==0) begin
                        assert(interruption_quota_o[k]==1'b0);
                    end else begin
                        //if the interrup was high, hold it high
                        if ($past(interruption_quota_o[k])==1'b1) begin
                            assert(interruption_quota_o[k]==1'b1);
                        end else begin
                            assert(interruption_quota_o[k]==1'b0);
                        end
                    end
                end
            end
        end
    end
*/ 
`endif
endmodule
`default_nettype wire //allow compatibility with legacy code and xilinx ip


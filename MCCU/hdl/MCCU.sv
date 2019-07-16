//-----------------------------------------------------
// ProjectName: PMU research 
// Function   : Implementation of Maximum-Contention Control Unit (MCCU): 
//              ResourceAccess Count and Contention Time Enforcement.
// Description: Mechanism assigns  
// Coder      : G.Cabo
// References : https://upcommons.upc.edu/handle/2117/133656

`default_nettype none
//`define DEBUG
`timescale 1 ns / 1 ps
	module MCCU #
	(
		// Width of data registers
		parameter integer DATA_WIDTH	= 32,
		// Width of weights registers
		parameter integer WEIGHTS_WIDTH	= 10,
        //Cores
        parameter integer N_CORES       =2,
        //Signals per core
        parameter integer CORE_EVENTS  =4
	)
	(
		input wire clk_i,
        //Active low asyncronous reset. It can have hardware or software source
		input wire rstn_i,
		//TODO: Add enable signal, active high
        input wire enable_i,
        //Monitored events that can generate contention in the system
        input wire [CORE_EVENTS-1:0] events_i [0:N_CORES-1],
        //Quota for each of the cores, internally registered, set by software
        input wire [DATA_WIDTH-1:0] quota_i [0:N_CORES-1],
        output wire [DATA_WIDTH-1:0] quota_o [0:N_CORES-1],
        //Worst contention that  each of the previous events can generate,
        //internally registered, set by software, if 0 event is dissabled
        input wire [WEIGHTS_WIDTH-1:0] events_weights_i [0:N_CORES-1]
                                                       [0:CORE_EVENTS-1],
        //Quota interruption
        output wire interruption_quota_o[N_CORES-1:0]
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
    
    //internal registers
    reg [DATA_WIDTH-1:0] quota [0:N_CORES-1];
    reg [WEIGHTS_WIDTH-1:0] events_weights [0:N_CORES-1] [0:CORE_EVENTS-1];
    reg [OVERFLOW_PROT-1:0]ccc_suma[0:N_CORES-1];//Addition of current cycle
                                               //consumed quota
    `ifdef DEBUG
    reg [OVERFLOW_PROT-1:0] debug_ccc_suma;//Just one core
    reg [OVERFLOW_PROT-1:0] debug_ccc_suma_loop;//Just one core
    reg [WEIGHTS_WIDTH-1:0] debug_events_weights [0:CORE_EVENTS-1];//Just one core
    assign debug_events_weights = events_weights [0];//assign to core 0
    integer k;  
    integer debug_tmp = 0;
    `endif
    /*----------
    Generate one mechanism to monitor te quota for each of the cores in the
    SOC,
    ----------*/
    integer i;
    integer j;
    generate
        begin : GeneratedQuotaMonitor
            always @(posedge clk_i, negedge rstn_i) begin: AsyncReset
                /*----------
                Auxiliar variables
                ----------*/
                longint tmp_ccc_suma;//temporal addition of ccc_suma
                /*----------
                Reset 
                ----------*/
                if(0 == rstn_i) begin
                    /*----------
                    Async reset Quota
                    ----------*/
                    for (i=0; i<N_CORES; i=i+1) begin : ResetQuota
                        quota[i] <={DATA_WIDTH{1'b0}}; 
                    end
                    
                    /*----------
                    Async reset Events
                    ----------*/
                    for (i=0; i<N_CORES; i=i+1) begin : ResetEventsWeights
                        for (j=0; j<CORE_EVENTS; j=j+1) begin
                            events_weights [i][j] <={WEIGHTS_WIDTH{1'b0}};  
                        end
                    end
                    /*----------
                    Async reset current cycle consumed quota
                    ----------*/
                    for (i=0; i<N_CORES; i=i+1) begin : ResetiCCCQuota
                        ccc_suma[i] <={OVERFLOW_PROT{1'b0}}; 
                    end
                end else begin
                /*----------
                Normal operation
                ----------*/
                    /*----------
                    Set weights of events, as this module is used whith an 
                    axi-lite wrapper the values are already registered 
                    outside and only need to be forwarded. Apply the event as 
                    a mask. If the event is inactive in hte current cycle
                    0 is placed in events_weights for that event.
                    ----------*/
                    for (i=0; i<N_CORES; i=i+1) begin : SetEventsWeights
                        for (j=0; j<CORE_EVENTS; j=j+1) begin
                            if(events_i[i][j]) begin
                                events_weights [i][j] <=events_weights_i[i][j];  
                            end else begin
                                events_weights [i][j] <={WEIGHTS_WIDTH{1'b0}};  
                            end

                        end
                    end
                    /*----------
                    //Set initial quota, as this module is used in the
                    //axi-lite wrapper the values are already registered 
                    //outside and only need to be forwarded
                    ----------*/
                    for (i=0; i<N_CORES; i=i+1) begin : SetQuota
                        quota[i] <= quota_i[i]; 
                    end

                    /*----------
                    Add quotas of all active signals. The ones that are not
                    enabled are 0.
                    ----------*/
                    if(enable_i) begin
                        for (i=0; i<N_CORES; i=i+1) begin : AddEventsWeights
                            tmp_ccc_suma=0;
                            for (j=0; j<CORE_EVENTS; j=j+1) begin
                                    //Reguired to avoid warning. Blocking
                                    //Assigment is legal when usign temporal
                                    //variables.
                                    /* verilator lint_off BLKSEQ */
                                    tmp_ccc_suma ={{O_W_0PAD{1'b0}},events_weights[i][j]} + tmp_ccc_suma;  
                                    /* verilator lint_on BLKSEQ */
                            end
                            ccc_suma[i]<=tmp_ccc_suma;
                            `ifdef DEBUG
                            /* verilator lint_off WIDTH */
                            /* verilator lint_off BLKSEQ */
                            //This only applies when 4 events are available
                                if(i==0 && CORE_EVENTS==4) begin
                                    debug_ccc_suma <= debug_events_weights[0]+debug_events_weights[1]+debug_events_weights[2]+debug_events_weights[3];
                                    debug_tmp=0;
                                    for(k=0; k<CORE_EVENTS; k=k+1) begin
                                            debug_tmp  =debug_events_weights[k] + debug_tmp;  
                                    end
                                    debug_ccc_suma_loop <= debug_tmp;
                                end
                                assert(debug_ccc_suma == debug_ccc_suma_loop);
                            //disable BLKSeK for the temporal assigment of debug_tmp
                            /* verilator lint_on BLKSEQ */
                            /* verilator lint_on WIDTH */
                            `endif
                            end
                        end
                    end 
                    /*----------
                    Substract to the core quota the weight of each active
                    event during this cycle. If the event is active the value
                    of the weight is substracted, if not 0 is substracted.
                    ----------*/
                    if(enable_i) begin
                        for (i=0; i<N_CORES; i=i+1) begin : SubstractQuota
                            for (j=0; j<CORE_EVENTS; j=j+1) begin
                                    //underflow detection. Padding needed for
                                    // prevent width mismatch
                                    if( ccc_suma[i] > {{O_D_0PAD{1'b0}},quota[i]} )
                                    begin
                                        quota[i] <={DATA_WIDTH{1'b0}};  
                                    end else begin
                                        quota[i] <= quota[i] - ccc_suma[i][DATA_WIDTH-1:0];  
                                    end
                            end
                        end
                    end
                end
            end
            /*----------
            Generate interruptions for quota for each core. Interrupt triggers
            one cycle before the result is registered. There is no record of
            by how much the quota was exceeded.
            ----------*/
            genvar x;
            for(x=0; x<N_CORES; x=x+1)  begin: InterruptionQuota
                assign interruption_quota_o[x] =(ccc_suma[x]>
                                                {{O_D_0PAD{1'b0}},quota[x]}
                                                )? 1'b1:1'b0;
            end
            /*----------
            forward results of internal registers 
            ----------*/
            assign quota_o = quota;
    endgenerate
endmodule
`default_nettype wire //allow compatibility with legacy code and xilinx ip


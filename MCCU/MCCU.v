//-----------------------------------------------------
// ProjectName: PMU research 
// Function   : Implementation of Maximum-Contention Control Unit (MCCU): 
//              ResourceAccess Count and Contention Time Enforcement.
// Description: Mechanism assigns  
// Coder      : G.Cabo
// References : https://upcommons.upc.edu/handle/2117/133656

`default_nettype none

`timescale 1 ns / 1 ps
//TODO:remove this
/* verilator lint_off UNUSED */
/* verilator lint_off UNDRIVEN */
/* verilator lint_off BLKSEQ */
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
        //Active low asyncronous reset
		input wire rstn_i,
		//Enable signal, active high
        input wire en_i,
        //Monitored events that can generate contention in the system
        input wire [CORE_EVENTS-1:0] events_i [0:N_CORES-1],
        //Quota for each of the cores, internally registered, set by software
        input wire [DATA_WIDTH-1:0] quota_i [0:N_CORES-1],
        output wire [DATA_WIDTH-1:0] quota_o [0:N_CORES-1],
        //Worst contention that  each of the previous events can generate,
        //internally registered, set by software, if 0 event is dissabled
        input wire [WEIGHTS_WIDTH-1:0] events_weights_i [0:N_CORES-1]
                                                       [0:CORE_EVENTS-1],
        output wire [WEIGHTS_WIDTH-1:0] events_weights_o [0:N_CORES-1]
                                                        [0:CORE_EVENTS-1],
        //Quota interruption
        output wire interruption_quota_o[N_CORES-1:0]
	);
    
    //internal registers
    reg [DATA_WIDTH-1:0] quota [0:N_CORES-1];
    reg [WEIGHTS_WIDTH-1:0] events_weights [0:N_CORES-1] [0:CORE_EVENTS-1];

    /*----------
    Generate one mechanism to monitor te quota for each of the cores in the
    SOC,
    ----------*/
    //genvar x;
    genvar i;
    genvar j;
    generate
        begin : GeneratedQuotaMonitor
            always @(posedge clk_i, negedge rstn_i) begin: AsyncReset
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
                            //TODO: Look why i can't have this secuential
                            events_weights [i][j] ={WEIGHTS_WIDTH{1'b0}};  
                        end
                    end
                end else begin
                /*----------
                Normal operation
                ----------*/
                    /*----------
                    Set weights of events, as this module is used in the    
                    an axi-lite wrapper the values are already registered 
                    outside and only need to be forwarded
                    ----------*/
                    for (i=0; i<N_CORES; i=i+1) begin : SetEventsWeights
                        for (i=0; i<CORE_EVENTS; i=i+1) begin
                            //TODO: Look why i can't have this secuential
                            events_weights [i][j] =events_weights_i[i][j];  
                        end
                    end
                    /*----------
                    //Set initial quota, as this module is used in the
                    //an axi-lite wrapper the values are already registered 
                    //outside and only need to be forwarded
                    ----------*/
                    for (i=0; i<N_CORES; i=i+1) begin : SetQuota
                        quota[i] <= quota_i[i]; 
                    end
                    /*----------
                    Substract to the core quota the weight of each active
                    event during this cycle. If the event is active the value
                    of the weight is substracted, if not 0 is substracted.
                    ----------*/
                    for (i=0; i<N_CORES; i=i+1) begin : SubstractQuota
                    //TODO:?There is a partial addition down in comb
                    end
                    //check interruption            

                end
            end
            /*----------
            Add quotas of all signals. The ones that are not enabled are 0
            ----------*/
            //OVERFLOW_PROT can be reduced, needs to be a bit larger than 
            //DATA_WIDTH
            localparam integer OVERFLOW_PROT = DATA_WIDTH*2;
            wire[OVERFLOW_PROT-1:0]tmp[0:N_CORES];
            reg [OVERFLOW_PROT-1:0]suma[0:N_CORES];
            //avoid width mismatch when add: OVERFLOW_PROT + DATA_WIDTH
            localparam O_D_0PAD = OVERFLOW_PROT-DATA_WIDTH;
            //avoid width mismatch when add: DATA_WIDTH + WEIGHTS_WIDTH
            localparam D_W_0PAD = DATA_WIDTH-WEIGHTS_WIDTH;
            //avoid width mismatch when add: OVERFLOW_PROT + WEIGHTS_WIDTH
            localparam O_W_0PAD = OVERFLOW_PROT-WEIGHTS_WIDTH;
            //Generate interruptions for quota
            for(i=0; i<N_CORES; i=i+1)  begin: InterruptionQuota
                assign interruption_quota_o[i] =(suma[i]>
                                                {{O_D_0PAD{1'b0}},quota[i]}
                                                )? 1'b1:1'b0;
            end
            /*----------
            check active signals to be added. This will pass 0 to the adder
            if the event is not enabled. If several events are active the 
            adder will count them next cycle
            ----------*/
            wire [WEIGHTS_WIDTH-1:0] values_count[0:N_CORES] [0:CORE_EVENTS-1];
            for(i=0; i<N_CORES; i=i+1)  begin: CheckActiveEvents 
                for (j=0; j<CORE_EVENTS; j=j+1) begin : MaskInactiveEvents
                    //This assignation sets value to 0 at reset. When the event
                    //is 0 the  values_count is 0 as well. If the event is 1
                    //it passes the value of events_weights
                    assign values_count[i][j]=
                            (rstn_i== 1'b0)
                            ?{WEIGHTS_WIDTH{1'b0}}:
                            {WEIGHTS_WIDTH{events_i[i][j]}}
                            &events_weights[i][j];
                end
            end
            //Add the quotas in a combinational block
            always @(*) begin : AddQuotasComb
                    //For all cores
                    for(i=0; i<N_CORES; i=i+1)  begin: SumQuotas
                        tmp[i] =0;
                        //For all events
                        for (j=0; j<CORE_EVENTS; j=j+1) begin
                            //Add in tmp[i] the weight of all active events
                            //TODO: add only active weights not all events
                            tmp[i]={{O_W_0PAD{1'b0}},values_count[i][j]}
                                   +tmp[i];
                        end
                        suma[i]=tmp[i];
                    end
            end
        end 
    endgenerate
`default_nettype wire //allow compatibility with legacy code and xilinx ip
endmodule


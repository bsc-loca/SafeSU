//-----------------------------------------------------
// ProjectName: PMU research 
// Function   : Implementation of Maximum-Contention Control Unit (MCCU): 
//              ResourceAccess Count and Contention Time Enforcement.
// Description: Request Duration Counter module
//              Reports any signal exceeding the maximum expected quota.
// Coder      : G.Cabo
// References : https://upcommons.upc.edu/handle/2117/133656

`default_nettype none
//`define DEBUG

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
	module RDC #
	(
		// Width of data registers
		parameter integer DATA_WIDTH	= 32,
		// Width of weights registers
		parameter integer WEIGHTS_WIDTH	= 8,
        //Cores. Change this may break Verilator TB
        parameter integer N_CORES       =4,
        //Signals per core. Change this may break Verilator TB
        parameter integer CORE_EVENTS   =2
	)
	(
		input wire clk_i,
        //Active low syncronous reset. It can have hardware or software source
		input wire rstn_i,
		//Active high enable. If enabled MaxValue can increase and interruptions
        //can be generated
        input wire enable_i,
        //Monitored events that can generate contention in the system
        input wire [CORE_EVENTS-1:0] events_i [0:N_CORES-1],
        //Worst contention that  each of the previous events can generate,
        //internally registered, set by software, if 0 event is dissabled
        input wire [WEIGHTS_WIDTH-1:0] events_weights_i [0:N_CORES-1]
                                                       [0:CORE_EVENTS-1],
        //Event longer than specified weight , single bit
        output wire interruption_rdc_o,
        //Interruption vector to indicate signal exceeding weight
        output reg [CORE_EVENTS-1:0] interruption_vector_rdc_o [0:N_CORES-1],
        //High watermark for each event of a given core.
        output logic [WEIGHTS_WIDTH-1:0] watermark_o [0:N_CORES-1]
                                                    [0:CORE_EVENTS-1]

    );
    
//-------------Adders with reset
    //Inside the generate loop it creates as many counters as the parameter
    //N_COUNTERS. For each of them one max_value register is assigned.
   
    //When module is not enabled (!enable_i), reset is active (rstn_i=0) or
    //the events_i[k] signal for the counter[k] is low the resgister is set to 0
    
    //Each clock cycle if the input signal (events_i) for a given counter is
    //high at the positive edge of the clock the counter increases
    localparam N_COUNTERS = CORE_EVENTS * N_CORES;
    reg [WEIGHTS_WIDTH-1 : 0] max_value [0 : N_COUNTERS-1];
    //I need a bit to hold the interruption state until RCD is reset on
    //disabled once the interrupt is risen
    reg past_interruption_rdc_o;
    genvar x;
    genvar y;
    generate
    for(x=0;x<N_CORES;x++) begin
        for(y=0;y<CORE_EVENTS;y++) begin
            always_ff @(posedge clk_i) begin
                if(!rstn_i)
                    max_value[CORE_EVENTS*x+y] <={WEIGHTS_WIDTH{1'b0}};
                else begin
                    if(enable_i && events_i[x][y]) begin
                        if(max_value[CORE_EVENTS*x+y]=={WEIGHTS_WIDTH{1'b1}}) begin
                            max_value[CORE_EVENTS*x+y] <= max_value[CORE_EVENTS*x+y];
                        end else begin
                            max_value[CORE_EVENTS*x+y] <= max_value[CORE_EVENTS*x+y]+1'b1;
                        end
                    end else begin
                        max_value[CORE_EVENTS*x+y] <={WEIGHTS_WIDTH{1'b0}};
                    end
                end
            end
        end
    end
    endgenerate

    /*----------
    Generate interruptions if the pulse width of a signal is equal or  exceeds
    the event wheight.
    Interruption is only generated if the  RDC is enabled
    ----------*/
    wire [CORE_EVENTS-1:0] interruption_vector_int [0:N_CORES-1];
    generate
    for(x=0;x<N_CORES;x++) begin
        for(y=0;y<CORE_EVENTS;y++) begin
            assign interruption_vector_int[x][y] = 
                            (max_value[(x*CORE_EVENTS)+y]>=events_weights_i[x][y])?
                            1'b1 : 1'b0;
        end
    end
    endgenerate
    
    //Register the output of comparison, to identify offending signal
    always @(posedge clk_i) begin
            if(!rstn_i)
                interruption_vector_rdc_o <='{default:{CORE_EVENTS{1'b0}}};
            else if (!enable_i)
                interruption_vector_rdc_o <='{default:{CORE_EVENTS{1'b0}}};
            else
                //If the  previous value interruption_vector_rdc_o was holding
                //and interrupt you shall keep it
                for(int i=0; i<N_CORES;i++) begin
                    interruption_vector_rdc_o[i] <= interruption_vector_int[i] | interruption_vector_rdc_o[i] ;
                end
    end
    //unpack interruption_vector_int to do the or redution of interruption_rdc_o
    wire [CORE_EVENTS*N_CORES-1:0] unpacked_vector_rdc_int;
    generate
    for(x=0;x<N_CORES;x++) begin
        for(y=0;y<CORE_EVENTS;y++) begin
            assign unpacked_vector_rdc_int[(x*CORE_EVENTS)+y] 
                   = interruption_vector_int[x][y]; 
        end
    end
    endgenerate
    //Update past_interruption_rdc_o
    always @(posedge clk_i) begin
            if(!rstn_i)
                past_interruption_rdc_o <= 1'b0;
            else if (!enable_i)
                past_interruption_rdc_o <= 1'b0;
            else
                past_interruption_rdc_o <= interruption_rdc_o;
    end
   
    //output interrupt if new interrupt or already on interrupt state
    assign interruption_rdc_o = ((|unpacked_vector_rdc_int) || past_interruption_rdc_o) & enable_i;
//-------------Watermark registers
    logic [WEIGHTS_WIDTH-1 : 0] watermark_int [0 : N_COUNTERS-1];
    genvar q;
    generate
    for (q=0; q<N_COUNTERS; q=q+1) begin : generated_watermark
        always_ff @(posedge clk_i) begin
            if(!rstn_i) begin
                watermark_int[q] <={WEIGHTS_WIDTH{1'b0}};
            end else begin
                if(!enable_i) begin
                    watermark_int[q] <= watermark_int[q];
                end else begin
                    if (watermark_int[q] < max_value[q] )
                    watermark_int[q] <= max_value[q];
                end
            end
        end
    end
    endgenerate
    
    genvar n;
    // n for iterate over cores
    // q to iterate over signals
    for (n=0; n<N_CORES; n=n+1) begin
        for (q=0; q<CORE_EVENTS; q=q+1) begin
            assign watermark_o[n][q] = watermark_int[n*CORE_EVENTS+q];
        end
    end
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
    //Check that counters never overflows 
    for(x=0;x<N_CORES;x++) begin
        for(y=0;y<CORE_EVENTS;y++) begin
            assert property (max_value[CORE_EVENTS*x+y]=={WEIGHTS_WIDTH{1'b1}} 
                 and events_i[x][y]==1 and enable_i |=> 
                 max_value[CORE_EVENTS*x+y]=={WEIGHTS_WIDTH{1'b1}} or rstn_i==0);
        end
    end
      
    //Check that counters get to 0 in the next cycle if a signal is low
    for(x=0;x<N_CORES;x++) begin
        for(y=0;y<CORE_EVENTS;y++) begin
            assert property (events_i[x][y]==0 |=>  max_value[CORE_EVENTS*x+y]==0); 
        end
    end
    
    //Check that counters are map to the correct signals
    for(x=0;x<N_CORES;x++) begin
        for(y=0;y<CORE_EVENTS;y++) begin
            assert property (events_i[x][y]==1 and enable_i==1 and rstn_i==1 
                            |=> max_value[CORE_EVENTS*x+y] == {WEIGHTS_WIDTH{1'b1}} or 
                            max_value[CORE_EVENTS*x+y]== $past(max_value[CORE_EVENTS*x+y])+1
                            or rstn_i==0 or enable_i ==0 ); 
        end
    end
    
    for(x=0;x<N_CORES;x++) begin
        for(y=0;y<CORE_EVENTS;y++) begin
            cover property ((watermark_int[CORE_EVENTS*x+y] ==8'h10));
        end
    end
    
    //The counter can get to 0 without reset or disable the enable
    cover property ( f_past_valid and enable_i==1 and rstn_i==1 and events_i[0][0]==1
                    and $stable(enable_i) and $stable(rstn_i) and $stable(events_i[0][0])
                    |=> events_i[0][0]==0 and $stable(enable_i) and $stable(rstn_i)
                    ); 

`endif
endmodule
`default_nettype wire

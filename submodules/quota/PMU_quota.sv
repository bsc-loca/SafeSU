//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Submodule of the PMU to handle quota consumption of a single
//              core.
// Description: This module checks the content of the counters selected by the
//              mask register. The value of the selected counters is added and
//              compared against the quota limit register.  If the total quota 
//              is exceeded then an interrupt is risen.
//
//              To account for a given event a 1 must be set to the Quota mask 
//              register. When the mask is 0 the value is not accounted for the
//              quota.
//
//              The adition of counters is sequential, therefore you could
//              notice up to N cycles (where N is the number of counters
//              ) from the point that the quota is exceeded until the point
//              where the interrupt is risen. 
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
module PMU_quota #
	(
		// Width of counters registers
		parameter integer REG_WIDTH	= 32,
		// Amount of counters
		parameter integer N_COUNTERS	= 9,
        //Localparameters
        //TODO: extend if needed more control
        //localparam max_width = $clog2(N_COUNTERS)+REG_WIDTH
        localparam max_width = REG_WIDTH
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
        // Input wire from wrapper containing the values of the counters
        input wire [REG_WIDTH-1:0] counter_value_i [0:N_COUNTERS-1],
        // Soft Reset Signal from configuration registeres. This Signal is 
            // Active HIGH
		input wire  softrst_i,
        // Input wire from wrapper with the maximum allowed quota consumption
            //Quota is calculated with the
            //sum_all_counters (counter_value_i[n] * counter_quota_mask_i[n]) 
        input wire [max_width-1:0] quota_limit_i,
        // Input quota interrupt mask. Only counters with their corresponding
            // mask interrupt set to high can be added to compute towards the
            // total quota that triggers the interrupt
        input wire [N_COUNTERS-1:0] quota_mask_i, 
        // Interrupt quota
        output wire intr_quota_o 
	);

//-------------Quota
    //A quota consumption interruption is generated when the total of 
    //measured events exceeds the value set in quota_limit_i.
    
    //To account for a given event a 1 must be set to the correspondent bit in
    //quota_mask_i.
    //When the mask is 0 the value is not accounted for the quota.
    
    // Maximum width of counter to prevent overflow given the addition of N 
        //values of fix width
    // Mask counter values that are disabled
    wire [REG_WIDTH-1:0] masked_counter_value_int [0:N_COUNTERS-1];
    genvar x;
    generate
        //mask counter values
        for (x=0; x<N_COUNTERS; x=x+1) begin : mask_counters
            //when reset is eneabled the values are 0. If not reset
            // check the mask and pass the value of the counter if enabled
            assign masked_counter_value_int[x]=
                    (softrst_i || (rstn_i == 1'b0))
                    ? {REG_WIDTH{1'b0}} : {REG_WIDTH{quota_mask_i[x]}} & counter_value_i[x];
        end
    endgenerate
    
    //Add values of all the masked signals sequentially
    // state_int shall  jump to reset state if the mask changes
    wire new_mask;
    reg [N_COUNTERS-1:0] old_mask;
    always_ff @(posedge clk_i, negedge rstn_i) begin
        if(rstn_i == 1'b0 ) begin
            old_mask <= {N_COUNTERS{1'b0}};
        end else if(softrst_i) begin 
            old_mask <= {N_COUNTERS{1'b0}};
        end else begin
            old_mask <= quota_mask_i;
        end
    end
    assign new_mask = old_mask != quota_mask_i ? 1'b1: 1'b0;
        //generate  a freespining counter to add values masked registers
        //State 0 = Reset suma_int
        //State 1 = Add counter 0 + Suman_int
        // ...
        //State n = Add counter n + Suman_int
        //State 0 = Reset suma_int
        // ...
    localparam n_states = $clog2(N_COUNTERS+1);
    reg [n_states-1:0] state_int;
    always_ff @(posedge clk_i, negedge rstn_i) begin
        integer i;
        if(rstn_i == 1'b0 ) begin
                state_int <={n_states{1'b0}};
        end else if(softrst_i || new_mask) begin 
                state_int <={n_states{1'b0}};
        end else begin
            state_int <= state_int + 1 ;
        end
    end

    // One state per counter +  reset state -> $clog2(N_COUNTERS+1)

    localparam padding0 = max_width - REG_WIDTH;
    reg [max_width-1:0] suma_int;
    always_ff @(posedge clk_i, negedge rstn_i) begin
        integer i;
        if(rstn_i == 1'b0 ) begin
                suma_int <={max_width{1'b0}};
        end else begin
            if(softrst_i) begin
                suma_int <={max_width{1'b0}};
            end else begin          
                if(new_mask) begin
                    suma_int <={max_width{1'b0}};
                end else begin
                    suma_int <= suma_int + {{padding0{1'b0}},masked_counter_value_int[state_int]}; 
                end
            end
        end
    end

    //Check if quota is exceeded and generate interrupt
    assign intr_quota_o = (suma_int > quota_limit_i )
                        ? 1'b1 : 1'b0;

////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip

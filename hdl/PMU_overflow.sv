//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Submodule of the PMU to handle overflow of counters
// Description: This module checks the bus of reg_o coming out of the counters
//              module. It trigger the signal of overflow when all the bits of 
//              a given bus are high.
//
//              The counters in the bus have one bit map in  to the overflow 
//              interrupt mask. The index of the counter and the bit in the
//              mask register is the same.
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
module PMU_overflow #
	(
		// Width of counters registers
		parameter integer REG_WIDTH	= 32,
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
        // Input wire from wrapper containing the values of the counters
        input wire [REG_WIDTH-1:0] counter_regs_i [0:N_COUNTERS-1],
        // Input overflow interrupt mask. Only counters with their corresponding
            // mask interrupt set to high can trigger the overflow interrupt
            // If the mask is set to 0, the interrupt vector  mask will not be 
            // updated either
        input wire [N_COUNTERS-1:0] over_intr_mask_i, 
        // Global interrupt overflow
        output wire intr_overflow_o, 
        // Output of the Overflow interruption vector
        output wire [N_COUNTERS-1:0] over_intr_vect_o        
	);
//-------------Overflow
    
    //OR reduction to detect overflow of each counter
    wire overflow [0:N_COUNTERS-1];
    
    genvar i;
    generate
        for (i=0; i<N_COUNTERS; i=i+1) begin : OR_reduction_counters
            assign overflow[i]=|counter_regs_i[i];
        end
    endgenerate 
    //check the mask for the overflow signals
    wire [N_COUNTERS-1:0] masked_overflow ;
    
    generate 
            for (i=0; i<N_COUNTERS; i=i+1) begin : masking_overflow
                assign masked_overflow[i]=overflow[i] & over_intr_mask_i[i];
            end
    endgenerate
    
    //AND overflow and mask for each counter and OR reduc
    wire intr_overflow_int;
    assign intr_overflow_int=|masked_overflow;
    //Drive output interrupt
    assign intr_overflow_o = intr_overflow_int;
    
    //Set overflow internal interruption vector
    reg [N_COUNTERS-1:0] over_intr_vect_int;
    always_ff @(posedge clk_i, negedge rstn_i) begin
        integer i;
        if(rstn_i == 1'b0 ) begin
                over_intr_vect_int <={N_COUNTERS{1'b0}};
        end else begin
            if(softrst_i) over_intr_vect_int <={N_COUNTERS{1'b0}};
            else if(en_i) begin 
                    over_intr_vect_int <=masked_overflow;
            end
        end
    end
    
    //Drive output overflow interruption vector
    assign over_intr_vect_o = over_intr_vect_int; 

//TODO: fill formal propperties
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip


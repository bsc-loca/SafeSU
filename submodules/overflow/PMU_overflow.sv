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
    wire [N_COUNTERS-1:0] overflow;
    
    genvar i;
    generate
        for (i=0; i<N_COUNTERS; i=i+1) begin : OR_reduction_counters
            assign overflow[i]=&counter_regs_i[i];
        end
    endgenerate 
    //check the mask for the overflow signals
    wire [N_COUNTERS-1:0] masked_overflow ;
    
    generate 
            for (i=0; i<N_COUNTERS; i=i+1) begin : masking_overflow
                assign masked_overflow[i] = overflow[i] & over_intr_mask_i[i];
            end
    endgenerate
    
    wire unit_disabled;
    assign unit_disabled = (rstn_i==0) || (softrst_i==1) || (en_i==0);
    //Drive output interrupt
    assign intr_overflow_o =unit_disabled? 1'b0 : |masked_overflow; 

    //Drive output overflow interruption vector
    assign over_intr_vect_o = unit_disabled? '{default:0} : masked_overflow;

//TODO: fill formal propperties
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
    always@( posedge clk_i )
        f_past_valid <= 1'b1;
   
    //assume that if f_past is not valid you have to reset
    always @(*) begin
		if(0 == f_past_valid) begin
            assume(0 == rstn_i);
         end
    end

// intr never can be 1 if soft reset was active the previous cycle
    always@( posedge clk_i ) begin
        if ( (f_past_valid==1)
            && (softrst_i==1)
            )
        assert(
            (over_intr_vect_o == 9'b000000000)
            && (intr_overflow_o == 1'b0)
        );
    end
// intr never can be 1 if rstn_i was low the previous cycle
    always@( posedge clk_i ) begin
       if ( (f_past_valid==1)
            && (rstn_i==0)
            )
       assert(
            (over_intr_vect_o == 9'b000000000)
            && (intr_overflow_o == 1'b0)
       );
    end
// intr never can be 1 if en_i was low the previous cycle
    always@( posedge clk_i ) begin
       if ( (f_past_valid==1)
            && (en_i==0)
            )
       assert(
            (over_intr_vect_o == 9'b000000000)
            && (intr_overflow_o == 1'b0)
       );
    end
    // Cover interrupt is enable
    default clocking @(posedge clk_i); endclocking   
    cover property (intr_overflow_o==1 && f_past_valid );
    cover property (over_intr_vect_o == 9'b111111111 && f_past_valid );
    cover property (masked_overflow == 9'b111111111 && f_past_valid);
                
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip


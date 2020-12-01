//-----------------------------------------------------
// ProjectName: SELENE_pmu
// Function   : Submodule of the PMU to reconfigure input events of the PMU
//
// Description: This module takes the parameters N_IN (Number of SoC events)
//              and the N_OUT (Number of available counters) and generates a module
//              that allows to connect any input event to any available counter of the PMU
//              
//              This is achieved by placing one mux with N_IN inputs and a single
//              output for each event that the PMU can handle. 
//  
//              The module is intended to extend PMU_raw. Additional memory positions are
//              required to configure each mux.
// Coder      : G.Cabo
// References : 

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
module crossbar #
	(
		// Amount of outputs (Number of available PMU counters)
		parameter integer N_OUT	= 24,
		// Amount of inputs (Number of SoC events)
		parameter integer N_IN = 32,
        //Localparametersi
        localparam integer N_BITS_CFG = $clog2(N_IN)
	)
	(
		// Global Clock Signal
		input wire  clk_i,
		// Global Reset Signal. This Signal is Active LOW
		input wire  rstn_i,
        // Input vector
        input var vector_i [0:N_IN-1] ,
        // Output vector
        output logic vector_o [0:N_OUT-1],
        // Configuration
        input var [N_BITS_CFG-1:0] cfg_i [0:N_OUT-1]
	);
    
    genvar x;
    //Model muxes
    logic mux_int[0:N_OUT-1];
    generate
        for(x=0;x<N_OUT;x++) begin : mux
            //Assign the input based on the configuration value
            assign mux_int[x]=vector_i[(cfg_i [x])];
        end
    endgenerate
    //Register output and assign muxes output
    generate
        for(x=0;x<N_OUT;x++) begin : reg_out
            always_ff @(posedge clk_i, negedge rstn_i) begin
                    if (!rstn_i) begin
                        vector_o[x] <= 0;
                    end else begin
                        vector_o[x] <= mux_int[x];
                    end
            end
        end
    endgenerate
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
    assert(N_IN >= N_OUT);

`endif

endmodule
`default_nettype wire //allow compatibility with legacy code and xilinx ip


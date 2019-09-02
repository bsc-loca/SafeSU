//-----------------------------------------------------
// Project Name : Drac
// Function     : Wrapper of the PMU
// Description  : This module transform individual inputs to an unpacked array 
//                and passes the signals to the actual PMU
// Coder        : G.Cabo

`default_nettype none
`timescale 1 ns / 1 ps

	module AXI_PMU #
	(
		// Parameters of Axi Slave Bus Interface S_AXI
		parameter integer C_S_AXI_DATA_WIDTH	= 32,
		parameter integer C_S_AXI_ADDR_WIDTH	= 7
	)
	(
		// Ports of Axi Slave Bus Interface S_AXI
		input wire  S_AXI_ACLK_i,
		input wire  S_AXI_ARESETN_i,
		input wire [C_S_AXI_ADDR_WIDTH-1 : 0] S_AXI_AWADDR_i,
		input wire  S_AXI_AWVALID_i,
		output wire  S_AXI_AWREADY_o,
		input wire [C_S_AXI_DATA_WIDTH-1 : 0] S_AXI_WDATA_i,
		input wire [(C_S_AXI_DATA_WIDTH/8)-1 : 0] S_AXI_WSTRB_i,
		input wire  S_AXI_WVALID_i,
		output wire  S_AXI_WREADY_o,
		output wire [1 : 0] S_AXI_BRESP_o,
		output wire  S_AXI_BVALID_o,
		input wire  S_AXI_BREADY_i,
		input wire [C_S_AXI_ADDR_WIDTH-1 : 0] S_AXI_ARADDR_i,
		input wire  S_AXI_ARVALID_i,
		output wire  S_AXI_ARREADY_o,
		output wire [C_S_AXI_DATA_WIDTH-1 : 0] S_AXI_RDATA_o,
		output wire [1 : 0] S_AXI_RRESP_o,
		output wire  S_AXI_RVALID_o,
		input wire  S_AXI_RREADY_i,
	
        //external signals to monitor
        input  wire        EV0_i            ,// signal  
        input  wire        EV1_i            ,// signal  
        input  wire        EV2_i            ,// signal  
        input  wire        EV3_i            ,// signal  
        input  wire        EV4_i            ,// signal  
        input  wire        EV5_i            ,// signal  
        input  wire        EV6_i            ,// signal  
        input  wire        EV7_i            ,// signal  
        input  wire        EV8_i            ,// signal  
        input  wire        EV9_i            ,// signal  
        input  wire        EV10_i            ,// signal  
        input  wire        EV11_i            ,// signal  
        input  wire        EV12_i            ,// signal  
        input  wire        EV13_i            ,// signal  
        input  wire        EV14_i            ,// signal  
        input  wire        EV15_i            ,// signal  
        
        //outputs
        output wire        int_overflow_o,
        output wire        int_quota_o,
        
        //MCCU io
        output wire        int_quota_c0_o,
        output wire        int_quota_c1_o
    );
    
    localparam integer N_COUNTERS	= 16;
    // Configuration registers
    localparam integer N_CONF_REGS	= 5;
    wire [N_COUNTERS-1:0] events_i;
    // Assign individual signals to packed array 
    assign events_i= { EV15_i,
                         EV14_i,
                         EV13_i,
                         EV12_i,
                         EV11_i,
                         EV10_i,
                         EV9_i,
                         EV8_i,
                         EV7_i,
                         EV6_i,
                         EV5_i,
                         EV4_i,
                         EV3_i,
                         EV2_i,
                         EV1_i,
                         EV0_i
                        };
    localparam N_CORES = 2;
    wire MCCU_int_o [N_CORES-1:0];
    //TODO: MCCU_int_o is not assigned parametrically
        //A pack array will look better. Consider chang it on the MCCU
    // Assign individual signals to unpacked array 
    assign int_quota_c0_o = MCCU_int_o[0];
    assign int_quota_c1_o = MCCU_int_o[1];
   
    // Instantiation of PMU
    AXI_PMU_interface_v1_0_S00_AXI # ( 
        .C_S_AXI_DATA_WIDTH(C_S_AXI_DATA_WIDTH),
        .C_S_AXI_ADDR_WIDTH(C_S_AXI_ADDR_WIDTH),
        .N_COUNTERS(N_COUNTERS),
        .N_CONF_REGS(N_CONF_REGS),
		.OVERFLOW(1), //No
		.QUOTA(1), //No
		.MCCU(1), //Yes
        .N_CORES(2)
    ) inst_AXI_PMU (
        .*
/*        .S_AXI_ACLK_i(S_AXI_ACLK_i),
        .S_AXI_ARESETN_i(S_AXI_ARESETN_i),
        .S_AXI_AWADDR_i(S_AXI_AWADDR_i),
        .S_AXI_AWVALID_i(S_AXI_AWVALID_i),
        .S_AXI_AWREADY_o(S_AXI_AWREADY_o),
        .S_AXI_WDATA_i(S_AXI_WDATA_i),
        .S_AXI_WSTRB_i(S_AXI_WSTRB_i),
        .S_AXI_WVALID_i(S_AXI_WVALID_i),
        .S_AXI_WREADY_o(S_AXI_WREADY_o),
        .S_AXI_BRESP_o(S_AXI_BRESP_o),
        .S_AXI_BVALID_o(S_AXI_BVALID_o),
        .S_AXI_BREADY_i(S_AXI_BREADY_i),
        .S_AXI_ARADDR_i(S_AXI_ARADDR_i),
        .S_AXI_ARVALID_i(S_AXI_ARVALID_i),
        .S_AXI_ARREADY_o(S_AXI_ARREADY_o),
        .S_AXI_RDATA_o(S_AXI_RDATA_o),
        .S_AXI_RRESP_o(S_AXI_RRESP_o),
        .S_AXI_RVALID_o(S_AXI_RVALID_o),
        .S_AXI_RREADY_i(S_AXI_RREADY_i),
        .events_i(events_i),
        .int_overflow_o(int_overflow_o),
        .int_quota_o(int_quota_o)*/

    );
	endmodule

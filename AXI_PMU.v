
`timescale 1 ns / 1 ps

	module AXI_PMU #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line


		// Parameters of Axi Slave Bus Interface S00_AXI
		parameter integer C_S00_AXI_DATA_WIDTH	= 32,
		parameter integer C_S00_AXI_ADDR_WIDTH	= 7
	)
	(
		// Users to add ports here

		// User ports ends
		// Do not modify the ports beyond this line


		// Ports of Axi Slave Bus Interface S00_AXI
		input wire  S_AXI_ACLK,
		input wire  S_AXI_ARESETN,
		input wire [C_S00_AXI_ADDR_WIDTH-1 : 0] S_AXI_AWADDR,
		input wire [2 : 0] S_AXI_AWPROT,
		input wire  S_AXI_AWVALID,
		output wire  S_AXI_AWREADY,
		input wire [C_S00_AXI_DATA_WIDTH-1 : 0] S_AXI_WDATA,
		input wire [(C_S00_AXI_DATA_WIDTH/8)-1 : 0] S_AXI_WSTRB,
		input wire  S_AXI_WVALID,
		output wire  S_AXI_WREADY,
		output wire [1 : 0] S_AXI_BRESP,
		output wire  S_AXI_BVALID,
		input wire  S_AXI_BREADY,
		input wire [C_S00_AXI_ADDR_WIDTH-1 : 0] S_AXI_ARADDR,
		input wire [2 : 0] S_AXI_ARPROT,
		input wire  S_AXI_ARVALID,
		output wire  S_AXI_ARREADY,
		output wire [C_S00_AXI_DATA_WIDTH-1 : 0] S_AXI_RDATA,
		output wire [1 : 0] S_AXI_RRESP,
		output wire  S_AXI_RVALID,
		input wire  S_AXI_RREADY,
	
        //external signals to monitor
        input  wire        EV0            ,// signal  
        input  wire        EV1            ,// signal  
        input  wire        EV2            ,// signal  
        input  wire        EV3            ,// signal  
        input  wire        EV4            ,// signal  
        input  wire        EV5            ,// signal  
        input  wire        EV6            ,// signal  
        input  wire        EV7            ,// signal  
        input  wire        EV8            ,// signal  
        input  wire        EV9            ,// signal  
        input  wire        EV10            ,// signal  
        input  wire        EV11            ,// signal  
        input  wire        EV12            ,// signal  
        input  wire        EV13            ,// signal  
        input  wire        EV14            ,// signal  
        input  wire        EV15            // signal  
    );
		localparam integer N_COUNTERS	= 16;
		// Configuration registers
		localparam integer N_CONF_REGS	= 5;
// Instantiation of Axi Bus Interface S00_AXI
	wire [N_COUNTERS-1:0] EVents;
    assign events = {EV0,
                         EV1,
                         EV2,
                         EV3,
                         EV4,
                         EV5,
                         EV6,
                         EV7,
                         EV8,
                         EV9,
                         EV10,
                         EV11,
                         EV12,
                         EV13,
                         EV14,
                         EV15
                        };

    AXI_PMU_interface_v1_0_S00_AXI # ( 
		.C_S_AXI_DATA_WIDTH(C_S00_AXI_DATA_WIDTH),
		.C_S_AXI_ADDR_WIDTH(C_S00_AXI_ADDR_WIDTH),
	    .N_COUNTERS(N_COUNTERS),
        .N_CONF_REGS(N_CONF_REGS)
    ) AXI_PMU_inst (
		.S_AXI_ACLK(S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),
		.S_AXI_AWADDR(S_AXI_AWADDR),
		.S_AXI_AWPROT(S_AXI_AWPROT),
		.S_AXI_AWVALID(S_AXI_AWVALID),
		.S_AXI_AWREADY(S_AXI_AWREADY),
		.S_AXI_WDATA(S_AXI_WDATA),
		.S_AXI_WSTRB(S_AXI_WSTRB),
		.S_AXI_WVALID(S_AXI_WVALID),
		.S_AXI_WREADY(S_AXI_WREADY),
		.S_AXI_BRESP(S_AXI_BRESP),
		.S_AXI_BVALID(S_AXI_BVALID),
		.S_AXI_BREADY(S_AXI_BREADY),
		.S_AXI_ARADDR(S_AXI_ARADDR),
		.S_AXI_ARPROT(S_AXI_ARPROT),
		.S_AXI_ARVALID(S_AXI_ARVALID),
		.S_AXI_ARREADY(S_AXI_ARREADY),
		.S_AXI_RDATA(S_AXI_RDATA),
		.S_AXI_RRESP(S_AXI_RRESP),
		.S_AXI_RVALID(S_AXI_RVALID),
		.S_AXI_RREADY(S_AXI_RREADY),
        .events(events)
	);

	// Add user logic here

	// User logic ends

	endmodule

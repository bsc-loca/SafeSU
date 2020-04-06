//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Integrate a register bank and AHB-lite interface
// Description: AHB-lite interface implementation of a register bank 
//              
//              This module is responsible managing reads and writes from a
//              AHB master and sets internal registers 
//
// Coder      : G.Cabo
// References : AMBA 3 AHB-lite  specifications 
//              ARM IHI 0033A  
// Notes      : 

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
	module dummy_ahb #
	(
        parameter haddr = 0,                                                  
        parameter hmask  = 0,                                           
		// Total amount of registers
        parameter integer N_REGS = 10, 
		// Width of registers data bus
        parameter integer REG_WIDTH = 32,
        //haddr width
        localparam integer HADDR_WIDTH = 32,
        //hdata width
        localparam integer HDATA_WIDTH = 32
	)
	(
         input wire rstn_i,
         input wire clk_i,
    //  -- AHB bus slave interface                                              
        // slave select
        input wire         hsel_i,                               
        // previous transfer done 
        input wire         hreadyi_i,
        // address bus 
        input wire [HADDR_WIDTH-1:0]  haddr_i,
        // read/write 
        input wire         hwrite_i,
        // transfer type
        input wire [1:0]   htrans_i,
        // transfer size
        input wire [2:0]   hsize_i,
        // burst type
        input wire [2:0]   hburst_i,
        // write data bus
        input wire [HDATA_WIDTH-1:0]  hwdata_i,
        // prtection control
        input wire [3:0]   hprot_i,
        // locked access 
        input wire         hmastlock_i,
        // trasfer done 
        output wire        hreadyo_o,
        // response type
        output wire [1:0]  hresp_o,
        // read data bus
        output wire [HDATA_WIDTH-1:0] hrdata_o
// full AHB signals
        // current master
//        input wire [3:0]   hmaster_i,
        // split completion
//        output wire [15:0] hsplit_o
	);
//----------------------------------------------
//------------- Local parameters
//----------------------------------------------
// ** Types of bursts (hburst_i) ** 
    //Single burst
    localparam SINGLE = 3'b00;
    //Incrementing burst of undefined length
    localparam INCR = 3'b01;
    //4-beat wrapping burst
    localparam WRAP4 = 3'b010;
    //4-beat incrementing burst
    localparam INCR4 = 3'b011;
    //8-beat wrapping burst
    localparam WRAP8 = 3'b100;
    //8-beat incrementing burst
    localparam INCR8 = 3'b101;
    //16-beat wrapping burs
    localparam WRAP16 = 3'b110;
    //16-beat incrementing burst
    localparam INCR16 = 3'b111;

// ** Type of transfers (htrans_i) **
    localparam TRANS_IDLE = 2'b00;
    localparam TRANS_BUSY = 2'b01;
    localparam TRANS_NONSEQUENTIAL = 2'b10;
    localparam TRANS_SEQUENTIAL = 2'b11;

// ** Type of Ready outputs (hreadyo_o) **
    //PENDING. Transfer has to be extended one cycle more
    //COMPLETE. Transfer has finish
localparam READY_PENDING = 1'b0;
localparam READY_COMPLETE = 1'b1;

// ** Type of Response outputs (hresp_o)**
    //OKAY. Transfer has finish or has to be extended
    //ERROR. Transfer is not valid 
localparam READYO_OKAY = 1'b0;
localparam READYO_ERROR = 1'b1;

// ** Transfer status **
// **{{hresp_o},{hready_o}} 
localparam TRANSFER_PENDING = 2'b00;
localparam TRANSFER_SUCCESS_COMPLETE = 2'b01;
localparam TRANSFER_ERROR_RESP_1CYCLE = 2'b10;
localparam TRANSFER_ERROR_RESP_2CYCLE = 2'b11;

//----------------------------------------------
//------------- Data structures
//----------------------------------------------
var struct packed{
    logic select;
    logic write;
    logic master_ready;
    logic [HADDR_WIDTH-1:0] master_addr;
    logic [HDATA_WIDTH-1:0] master_data;
    logic [1:0] trans_type;
    logic [2:0] trans_size;
    logic [2:0] burst_type;
    logic [3:0] protection;
    logic lock;
} address_phase;

/* //TODO: clean up
var struct packed{
    logic slave_ready;
    logic [1:0] slave_resp;
    logic [HDATA_WIDTH-1:0] slave_data;
} data_phase;
*/
//----------------------------------------------
//------------- AHB registers
//----------------------------------------------
    logic [REG_WIDTH-1:0] slv_reg [0:N_REGS-1];
    logic [REG_WIDTH-1:0] slv_reg_D [0:N_REGS-1];
    logic [REG_WIDTH-1:0] slv_reg_Q [0:N_REGS-1];
    
    assign slv_reg_Q = slv_reg;

    always_ff @(posedge clk_i, negedge rstn_i) begin
        if(rstn_i == 1'b0 ) begin
            slv_reg<='{default:0};
        end else begin 
            slv_reg <= slv_reg_D;
        end
    end

//----------------------------------------------
//------------- AHB control logic
//----------------------------------------------
logic [1:0] state, next;

// address phase - state update 
always_comb begin
    case (htrans_i)
        TRANS_IDLE: begin
            next = TRANS_IDLE;
        end
        TRANS_BUSY:begin
            next = TRANS_BUSY;
        end
        TRANS_NONSEQUENTIAL:begin
            if(!hsel_i) begin
                next = TRANS_IDLE;
            end else begin
                next = TRANS_NONSEQUENTIAL;
            end
        end
        TRANS_SEQUENTIAL:begin
            if(!hsel_i) begin
                next = TRANS_IDLE;
            end else begin
                next = TRANS_SEQUENTIAL;
            end
        end
    endcase
end
// address phase - register required inputs
always_ff @(posedge clk_i, negedge rstn_i) begin
    if(rstn_i == 1'b0 ) begin
        //initialize all the structure to  0 at reset
        address_phase <= '{default:0};
    end else begin 
        case (next) 
            TRANS_IDLE:begin
                address_phase.select <= hsel_i;
                address_phase.write <= hwrite_i;
            end
            TRANS_BUSY:begin
                address_phase.select <= hsel_i;
                address_phase.write <= hwrite_i;
            end
            TRANS_NONSEQUENTIAL:begin
                address_phase.select <= hsel_i;
                address_phase.write <= hwrite_i;
                address_phase.master_ready <= hreadyi_i;
                address_phase.master_addr <= haddr_i;
               // address_phase.master_data <= hwdata_i;
                address_phase.trans_type <= htrans_i;
                //address_phase.trans_size <= hsize_i;
                //address_phase.burst_type <= hburst_i;
                //address_phase.protection <= hprot_i;
                //address_phase.lock <= hmastlock_i;
            end
            TRANS_SEQUENTIAL:begin
                address_phase.select <= hsel_i;
                address_phase.write <= hwrite_i;
                address_phase.master_ready <= hreadyi_i;
                address_phase.master_addr <= haddr_i;
               // address_phase.master_data <= hwdata_i;
                address_phase.trans_type <= htrans_i;
                //address_phase.trans_size <= hsize_i;
                //address_phase.burst_type <= hburst_i;
                //address_phase.protection <= hprot_i;
                //address_phase.lock <= hmastlock_i;
            end
        endcase
    end
end

//data phase - state update
always_ff @(posedge clk_i, negedge rstn_i) begin
    if(rstn_i == 1'b0 ) begin
        state<=TRANS_IDLE;
    end else begin 
        state <= next;
    end
end

//data phase - slave response
wire [$clog2(N_REGS)-1:0] slv_index;
logic [HDATA_WIDTH-1:0] dwrite_slave; //Data master to the register bank
assign slv_index = address_phase.master_addr[$clog2(N_REGS)+1:2];
logic [1:0] complete_transfer_status;
logic [HDATA_WIDTH-1:0] dread_slave; //response from slave
assign hrdata_o = dread_slave;

assign hreadyo_o = complete_transfer_status [0];
//TODO: review the amount of bits for hresp_o
assign hresp_o = {{complete_transfer_status[1]},{complete_transfer_status[1]}};

//TODO: review
//dread_slave and dwrite_slave can be latched
//They will be ignored by the master and slave registers
always_latch begin
    case (state)
        TRANS_IDLE: begin
            complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
        end
        TRANS_BUSY:begin
            complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
        end
        TRANS_NONSEQUENTIAL:begin
            complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
            dwrite_slave = hwdata_i; 
            if (!address_phase.write) begin
                dread_slave = slv_reg_Q[slv_index];
            end 
        end
        TRANS_SEQUENTIAL:begin
            complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
            dwrite_slave = hwdata_i; 
            if (!address_phase.write) begin
                dread_slave = slv_reg_Q[slv_index];
            end
        end
    endcase
end
//----------------------------------------------
//------------- Slave registers update
//----------------------------------------------

//Each cycle the values in slv_reg_D will be saved in slv_reg
    //So if you want to update slv_reg the values for slv_reg_D shall be 
    //assigned in this section
    //If you add aditional logic that can cahnge the values of the registers
    //the next always block have to be modified to add the aditional
    //conditions under which the slv_reg shall be updated
         
always_comb begin
    //AHB write
    //Write to slv registers if slave was selected &  was a write 
    if(address_phase.write && address_phase.select) begin
        slv_reg_D=slv_reg_Q;
        slv_reg_D[slv_index] = dwrite_slave; 
    end else begin
        slv_reg_D=slv_reg_Q;
    end
end
endmodule
`default_nettype wire //allow compatibility with legacy code and xilinx ip

/*
    //  -- AHB bus slave interface                                              
        // burst type
        // write data bus
        input wire [HDATA_WIDTH-1:0]  hwdata_i,
        // prtection control
        input wire [3:0]   hprot_i,
        // transfer done 
        input wire         hreadyi_i,
        // current master
        input wire [3:0]   hmaster_i,
        // locked access 
        input wire         hmastlock_i,
        // trasfer done 
        output wire        hreadyo_o,
        // response type
        output wire [1:0]  hresp_o,
        // read data bus
        output wire [HDATA_WIDTH-1:0] hrdata_o,
        // split completion
        output wire [15:0] hsplit_o
//------------- AHB Basic functions
        input wire rstn_i,
        input wire clk_i,
        input wire         hsel_i,                               
        input wire [HADDR_WIDTH-1:0]  haddr_i,
        input wire         hwrite_i,
        input wire [1:0]   htrans_i,
        input wire [2:0]   hsize_i,
//------------- AHB Bursts
        input wire [1:0]   htrans_i,
        input wire [2:0]   hburst_i,
//------------- AHB Locked transfers 
//------------- AHB Protection control
//------------- AHB Bursts
//------------- AHB Bursts
                
                address_phase.select <= hsel_i;
                address_phase.write <= hwrite_i;
                address_phase.master_ready <= hreadyi_i;
                address_phase.master_addr <= haddr_i;
                address_phase.master_data <= hwdata_i;
                address_phase.trans_type <= htrans_i;
                address_phase.trans_size <= hsize_i;
                address_phase.burst_type <= hburst_i;
                address_phase.protection <= hprot_i;
                address_phase.lock <= hmastlock_i;
    logic slave_ready;
    logic [1:0] slave_resp;
    logic [HDATA_WIDTH-1:0] slave_data;
            data_phase.slave_ready <= ;
            data_phase.slave_resp <= ;
            data_phase.slave_data <= ;
* */


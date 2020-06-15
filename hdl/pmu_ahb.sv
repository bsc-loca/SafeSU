//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Integrate PMU and AHB interface
// Description: AHB interface implementation of the  PMU. 
//              
//              This module is responsible managing reads and writes from and
//              AHB master and interface with pmu_ahb module.
//
// Coder      : G.Cabo
// References : AMBA 3 AHB-lite  specifications 
//              ARM IHI 0033A  
// Notes      : Any write to a control registers takes 2 clock cycles to
//              take effect since it propagates from the wrapper to the
//              internal regs of the PMU

`default_nettype none
`timescale 1 ns / 1 ps

`ifndef SYNT
    `ifdef FORMAL 
        `define ASSERTIONS
    `endif
`endif
	module pmu_ahb #
	(
        parameter haddr = 0,                                                  
        parameter hmask  = 0,                                           
		// Width of registers data bus
        parameter integer REG_WIDTH = 32,
        //haddr width
        localparam integer HADDR_WIDTH = 32,
        //hdata width
        localparam integer HDATA_WIDTH = 32,
        //Required for MCCU interrupts
    // -- PMU specific parameters
        // Cores connected to MCCU
        localparam MCCU_N_CORES = 4,
		// Total amount of registers
        parameter integer N_REGS = 26, 
        // Number of configuration registers
        localparam PMU_CFG = 1,
        // Number of counters
        localparam PMU_COUNTERS = 9,
        //TODO: for now it is hardcoded but this may be calculated given the
        //features, n_cores and N_events in the future
        localparam PMU_TOTAL_REGS = N_REGS
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
        output wire [HDATA_WIDTH-1:0] hrdata_o,
    // -- PMU specific signales
        input wire [PMU_COUNTERS-1:0] events_i,
        //interruption rises when one of the counters overflows
        output wire intr_overflow_o,
        //interruption rises when overal events quota is exceeded 
        output wire intr_quota_o,
        // MCCU interruption for exceeded quota. One signal per core
        output wire [MCCU_N_CORES-1:0] intr_MCCU_o,
        // RDC (Request Duration Counter) interruption for exceeded quota
        output wire intr_RDC_o
    );
    //----------------------------------------------
    // VIVADO: list of debug signals for ILA 
    //----------------------------------------------   
    `define ILA_DEBUG_PMU_AHB
    `ifdef ILA_DEBUG_PMU_AHB                                              
    (* MARK_DEBUG = "TRUE" *) wire debug_hsel_i     ;        
    (* MARK_DEBUG = "TRUE" *) wire [HADDR_WIDTH-1:0] debug_haddr_i     ;       
    (* MARK_DEBUG = "TRUE" *) wire debug_hwrite_i    ;       
    (* MARK_DEBUG = "TRUE" *) wire [1:0] debug_htrans_i    ;       
    (* MARK_DEBUG = "TRUE" *) wire [2:0] debug_hsize_i     ;       
    (* MARK_DEBUG = "TRUE" *) wire [2:0] debug_hburst_i    ;       
    (* MARK_DEBUG = "TRUE" *) wire [HDATA_WIDTH-1:0] debug_hwdata_i    ;       
    (* MARK_DEBUG = "TRUE" *) wire debug_hprot_i     ;       
    (* MARK_DEBUG = "TRUE" *) wire debug_hreadyi_i   ;       
    (* MARK_DEBUG = "TRUE" *) wire debug_hmastlock_i ;       
    (* MARK_DEBUG = "TRUE" *) wire debug_hreadyo_o   ;       
    (* MARK_DEBUG = "TRUE" *) wire [1:0] debug_hresp_o     ;       
    (* MARK_DEBUG = "TRUE" *) wire [HDATA_WIDTH-1:0] debug_hrdata_o    ;       
    (* MARK_DEBUG = "TRUE" *) wire [PMU_COUNTERS-1:0] debug_events_i   ;        
    (* MARK_DEBUG = "TRUE" *) wire debug_intr_overflow_o;    
    (* MARK_DEBUG = "TRUE" *) wire debug_intr_quota_o;       
    (* MARK_DEBUG = "TRUE" *) wire [MCCU_N_CORES-1:0] debug_intr_MCCU_o;        
    (* MARK_DEBUG = "TRUE" *) wire debug_intr_RDC_o;         
    assign debug_hsel_i   = hsel_i;                                                      
    assign debug_haddr_i = haddr_i;                          
    assign debug_hwrite_i = hwrite_i;                        
    assign debug_htrans_i = htrans_i;                        
    assign debug_hsize_i = hsize_i;                          
    assign debug_hburst_i = hburst_i;                        
    assign debug_hwdata_i = hwdata_i;                        
    assign debug_hprot_i = hprot_i;                          
    assign debug_hreadyi_i = hreadyi_i;                      
    assign debug_hmastlock_i = hmastlock_i;                  
    assign debug_hreadyo_o = hreadyo_o;                      
    assign debug_hresp_o = hresp_o;                          
    assign debug_hrdata_o = hrdata_o;                        
    assign debug_events_i = events_i;                        
    assign debug_intr_overflow_o = intr_overflow_o;          
    assign debug_intr_quota_o = intr_quota_o;                
    assign debug_intr_MCCU_o = intr_MCCU_o;                  
    assign debug_intr_RDC_o = intr_RDC_o ;  
    `endif                                                                                                              
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
//    logic master_ready;
    logic [HADDR_WIDTH-1:0] master_addr;
} address_phase;

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
            if(!hsel_i) begin
                next = TRANS_IDLE;
            end else begin
                next = TRANS_BUSY;
            end
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
                address_phase.write <= 0; 
            end
            TRANS_BUSY:begin
                address_phase.select <= hsel_i;
                address_phase.write <= 0;
            end
            TRANS_NONSEQUENTIAL:begin
                address_phase.select <= hsel_i;
                address_phase.write <= hwrite_i;
                address_phase.master_addr <= haddr_i;
            end
            TRANS_SEQUENTIAL:begin
                address_phase.select <= hsel_i;
                address_phase.write <= hwrite_i;
                address_phase.master_addr <= haddr_i;
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

always_comb begin
//NOTE: I don't expect any of the cafe beaf values in the registers if they do
//there is a bug
    case (state)
        TRANS_IDLE: begin
            complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
            dwrite_slave = 32'hbeaf1d1e; 
            dread_slave = 32'hcafe1d1e; 
        end
        TRANS_BUSY:begin
            complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
            dwrite_slave = 32'hbeafb551; 
            dread_slave = 32'hcafeb551; 
        end
        TRANS_NONSEQUENTIAL:begin
            complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
            dwrite_slave = hwdata_i; 
            if (!address_phase.write) begin
                dread_slave = slv_reg_Q[slv_index];
            end else begin
                dread_slave = 32'hcafe01a1;
            end
        end
        TRANS_SEQUENTIAL:begin
            complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
            dwrite_slave = hwdata_i; 
            if (!address_phase.write) begin
                dread_slave = slv_reg_Q[slv_index];
            end else begin
                dread_slave = 32'hcafee1a1;
            end
        end
    endcase
end

//----------------------------------------------
//------------- PMU_raw instance
//----------------------------------------------
    //assert(PMU_TOTAL_REGS == N_REGS);
    wire [REG_WIDTH-1:0] pmu_regs_int [0:N_REGS-1];
    wire ahb_write_req;
    assign ahb_write_req = address_phase.write && address_phase.select;
    logic delay1_ahb_write_req; 
    logic [REG_WIDTH-1:0]delay1_dwrite_slave;
    logic [$clog2(N_REGS)-1:0] delay1_slv_index;
    //sice the modules that recieve the .wrapper_we_i get the value from
    //slv_reg_Q it needs one cycle of delay to get the right value
    //To avoid update the vaule of the slv_reg with old values from the PMU
    //after a write slv_index dwrite_slave ahb_write_req are held for one
    //cycle until the value is updated in .regs_o
    always_ff @(posedge clk_i, negedge rstn_i) begin
        if(rstn_i == 1'b0 ) begin
            delay1_ahb_write_req <= 0; 
            delay1_dwrite_slave <= 0; 
            delay1_slv_index <= 0; 
        end else begin
            delay1_ahb_write_req <= ahb_write_req;
            delay1_dwrite_slave <= dwrite_slave; 
            delay1_slv_index <= slv_index; 
        end
    end
    PMU_raw #(
		.REG_WIDTH(REG_WIDTH),
		.N_COUNTERS(PMU_COUNTERS),
		.N_CONF_REGS(PMU_CFG)
	)inst_pmu_raw (
		.clk_i(clk_i),
		.rstn_i(rstn_i),
        .regs_i(slv_reg_Q),
        .regs_o(pmu_regs_int),
        .wrapper_we_i(delay1_ahb_write_req),
        //on pourpose .name connections
        .events_i,
        .intr_overflow_o,
        .intr_quota_o,
        .intr_MCCU_o,
        .intr_RDC_o
	);

//----------------------------------------------
//------------- Slave registers update
//----------------------------------------------

//Each cycle the values in slv_reg_D will be saved in slv_reg
    //So if you want to update slv_reg the values for slv_reg_D shall be 
    //assigned in this section
    //If you add aditional logic that can change the values of the registers
    //the next always block have to be modified to add the aditional
    //conditions under which the slv_reg shall be updated

always_comb begin
    //AHB write
    //Write to slv registers if slave was selected & was a write. Else
    //register the values given by pmu_raw
    if(address_phase.write && address_phase.select) begin
        // get the values from the pmu_raw instance
        slv_reg_D=pmu_regs_int;
        //If there is a write pending to be written and is not overwritten 
            //for the current write update two registers, else write only the
            //most recent value
        if(delay1_ahb_write_req && (delay1_slv_index!=slv_index)) begin
            slv_reg_D[delay1_slv_index] = delay1_dwrite_slave; 
            slv_reg_D[slv_index] = dwrite_slave; 
        end else begin
            slv_reg_D[slv_index] = dwrite_slave; 
        end
    end else begin
            slv_reg_D=pmu_regs_int;
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
    //AHB assumptions


    default clocking @(posedge clk_i); endclocking;
    //If the peripheral is not selected there is no chance to issue a write
    assert property (((hsel_i == 0) && f_past_valid 
                    ) 
                    |=> (ahb_write_req == 0));

    //If htrans_i is not iddle or busy and  there is a write. ahb_write_req is
    //one in the next cycle unless there is a reset in the next cycle
    assert property (((hsel_i == 1) && f_past_valid && rstn_i==1 && $stable(rstn_i) 
                    && (htrans_i!=TRANS_IDLE && htrans_i!=TRANS_BUSY)
                    && (hwrite_i==1)
                    )
                    |=> (ahb_write_req == 1) || rstn_i==0);
    // If event 8 is low and current transaction is not a write, counter is
    // stable
    assert property ((events_i[8]==0 && $stable(events_i[8]) &&
                    ahb_write_req==0
                     )
                     |=> $stable(slv_reg[9]) ||
                         (slv_reg[9]==($past(slv_reg[9])+1)) 
                         || $past(rstn_i)==1);

    //*** TODO: Rewrite as a single assertion ***/
    //Can a counter report something different to 0 if no write and no event
    //is active? No
    //assume property (slv_index!=9 && events_i[8]==0);
    //assume we are not in selftest
    //assume property (slv_index==0 |-> hwdata_i[31:30] == 0);
    //assert property (slv_reg[9]==0);


`endif

endmodule
`default_nettype wire //allow compatibility with legacy code and xilinx ip

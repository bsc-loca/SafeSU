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
        parameter integer haddr = 0,                                                  
        parameter integer hmask  = 0,                                           
		// Width of registers data bus
        parameter integer REG_WIDTH = 32,
        // Number of counters
        parameter integer PMU_COUNTERS = 24,
        // Number of SoC events
	    parameter integer N_SOC_EV = 128,
	// Total amount of registers (use ahb_pmu_mem_map.ods) 
        parameter integer N_REGS = 55, 
        // Fault tolerance mechanisms (FT==0 -> FT disabled)
        parameter integer FT  = 0,                                           
	// -- Local parameters
		//haddr width
        localparam integer HADDR_WIDTH = 32,
		//hdata width
        localparam integer HDATA_WIDTH = 32,
		// Cores connected to MCCU
        parameter MCCU_N_CORES = 6,
		// Number of configuration registers
        localparam PMU_CFG = 1
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
        input wire [N_SOC_EV-1:0] events_i,
        //interruption rises when one of the counters overflows
        output wire intr_overflow_o,
        //interruption rises when overal events quota is exceeded 
        output wire intr_quota_o,
        // MCCU interruption for exceeded quota. One signal per core
        output wire [MCCU_N_CORES-1:0] intr_MCCU_o,
        // RDC (Request Duration Counter) interruption for exceeded quota
        output wire intr_RDC_o,
        // FT (Fault tolerance) interrupt, error detected and recovered
        output wire intr_FT1_o,
        // FT (Fault tolerance) interrupt, error detected but not recoverable
        output wire intr_FT2_o
    );
    //----------------------------------------------
    // VIVADO: list of debug signals for ILA 
    //----------------------------------------------   
    `ifdef ILA_DEBUG_PMU_AHB                                              
    (* MARK_DEBUG = "TRUE" *) wire debug_hsel_i     ;        
    (* MARK_DEBUG = "TRUE" *) wire [HADDR_WIDTH-1:0] debug_haddr_i     ;       
    (* MARK_DEBUG = "TRUE" *) wire debug_hwrite_i    ;       
    (* MARK_DEBUG = "TRUE" *) wire [1:0] debug_htrans_i    ;       
    (* MARK_DEBUG = "TRUE" *) wire [2:0] debug_hsize_i     ;       
    (* MARK_DEBUG = "TRUE" *) wire [2:0] debug_hburst_i    ;       
    (* MARK_DEBUG = "TRUE" *) wire [HDATA_WIDTH-1:0] debug_hwdata_i    ;       
    (* MARK_DEBUG = "TRUE" *) wire [3:0] debug_hprot_i     ;       
    (* MARK_DEBUG = "TRUE" *) wire debug_hreadyi_i   ;       
    (* MARK_DEBUG = "TRUE" *) wire debug_hmastlock_i ;       
    (* MARK_DEBUG = "TRUE" *) wire debug_hreadyo_o   ;       
    (* MARK_DEBUG = "TRUE" *) wire [1:0] debug_hresp_o     ;       
    (* MARK_DEBUG = "TRUE" *) wire [HDATA_WIDTH-1:0] debug_hrdata_o    ;       
    (* MARK_DEBUG = "TRUE" *) wire [N_SOC_EV-1:0] debug_events_i   ;        
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
    logic select_D, select_Q;
    logic write_D, write_Q;
//    logic master_ready;
    logic [HADDR_WIDTH-1:0] master_addr_D, master_addr_Q;
} address_phase;
if (FT==0) begin
    logic select, write;
    logic [HADDR_WIDTH-1:0] master_addr;
    always_ff @(posedge clk_i) begin
        if (rstn_i==0) begin
            select <= 1'b0;
            write <= 1'b0;
            master_addr <= '{default:0};
        end else begin
            select <= address_phase.select_D;
            write <= address_phase. write_D;
            master_addr <= address_phase.master_addr_D;
        end
    end
    
    always_comb begin
        address_phase.select_Q = select;
        address_phase.write_Q = write;
        address_phase.master_addr_Q = master_addr;
    end
end else begin : Apft //Address phase FT
    logic write_fte1, select_fte1, master_addr_fte1;
    logic write_fte2, select_fte2, master_addr_fte2;
    
    triple_reg#(.IN_WIDTH(1)
    )write_trip(
    .clk_i(clk_i),
    .rstn_i(rstn_i),
    .din_i(address_phase.write_D),
    .dout_o(address_phase.write_Q),
    .error1_o(write_fte1), // ignore corrected errors
    .error2_o(write_fte2)
    );
    
    triple_reg#(.IN_WIDTH(1)
    )select_trip(
    .clk_i(clk_i),
    .rstn_i(rstn_i),
    .din_i(address_phase.select_D),
    .dout_o(address_phase.select_Q),
    .error1_o(select_fte1), // ignore corrected errors
    .error2_o(select_fte2)
    );
    
    triple_reg#(.IN_WIDTH(HADDR_WIDTH)
    )master_addr_trip(
    .clk_i(clk_i),
    .rstn_i(rstn_i),
    .din_i(address_phase.master_addr_D),
    .dout_o(address_phase.master_addr_Q),
    .error1_o(master_addr_fte1), // ignore corrected errors
    .error2_o(master_addr_fte2)
    );
    
end


//----------------------------------------------
//------------- AHB registers
//----------------------------------------------
    wire [REG_WIDTH-1:0] pmu_regs_int [0:N_REGS-1];
    logic [HDATA_WIDTH-1:0] dwrite_slave; //Data master to the register bank
    logic [1:0] complete_transfer_status;
    logic [HDATA_WIDTH-1:0] dread_slave; //response from slave
    wire [$clog2(N_REGS)-1:0] slv_index;
    wire  invalid_index;
    logic [REG_WIDTH-1:0] slv_reg [0:N_REGS-1];
    logic [REG_WIDTH-1:0] slv_reg_D [0:N_REGS-1];
    logic [REG_WIDTH-1:0] slv_reg_Q [0:N_REGS-1];
     
    generate
    if (FT==0) begin
        always_ff @(posedge clk_i) begin
            if(rstn_i == 1'b0 ) begin
                slv_reg<='{default:0};
            end else begin 
                slv_reg <= slv_reg_D;
            end
        end
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
                //Write to slv registers if slave was selected & was a write to a valid register
                //Else register the values given by pmu_raw
                if(address_phase.write_Q && address_phase.select_Q && !invalid_index) begin
                    // get the values from the pmu_raw instance
                    slv_reg_Q = slv_reg;
                    slv_reg_Q [slv_index] = dwrite_slave;
                    slv_reg_D = pmu_regs_int;
                    slv_reg_D[slv_index] = dwrite_slave; 
                end else begin
                    slv_reg_D = pmu_regs_int;
                    slv_reg_Q = slv_reg;
                end
        end 
    end else begin : Slvft
        //FT version of the registers
            // Hamming bits, 6 for each 26 bits of data
        localparam HAM_P=6;//protection bits
        localparam HAM_D=26;//data bits
        localparam HAM_M=HAM_P+HAM_D;//mesage bits
        localparam N_HAM32_SLV= (((REG_WIDTH*N_REGS)+(HAM_D-1))/(HAM_D));
            //interrupt FT error
        wire  [N_HAM32_SLV-1:0] ift_slv; //interrupt fault tolerance mechanism
            //"Flat" slv_reg Q and D signals
        wire [N_HAM32_SLV*HAM_D-1:0] slv_reg_fte;//fault tolerance in
        wire [N_HAM32_SLV*HAM_D-1:0] slv_reg_fto;//fault tolerance out
        wire [REG_WIDTH-1:0] slv_reg_ufto [0:N_REGS-1];//unpacked fault tolerance out
        wire [N_HAM32_SLV*HAM_D-1:0] slv_reg_pQ ;//protected output
            //"Flat" hamming messages (Data+parity bits)
        wire [(HAM_M*N_HAM32_SLV)-1:0] ham_mbits_D;
        wire [(HAM_M*N_HAM32_SLV)-1:0] ham_mbits_Q;
            //Registers for parity bits
        logic [HAM_P*N_HAM32_SLV-1:0] ham_pbits;
        //Feed and send flat assigment in to original format 
        for (genvar i =0; i<N_REGS; i++) begin
            //assign slv_register inputs to a flat hamming input
            assign slv_reg_fte[(i+1)*REG_WIDTH-1:i*REG_WIDTH]=slv_reg_D[i][REG_WIDTH-1:0];
        end
        // SEC-DEC hamming on 26 bit data chunks
        for (genvar i =0; i<(N_HAM32_SLV); i++) begin : slv_ham_enc
            //encoder
                //hv_o needs to inteleave protection and data bits
            hamming32t26d_enc#(
            )slv_hamming32t26d_enc (
                .data_i(slv_reg_fte[(i+1)*HAM_D-1:i*HAM_D]),
                .hv_o(ham_mbits_D[(i+1)*(HAM_M)-1:i*(HAM_M)])
            );
        end
        //Feed data into original registers
        for (genvar i =0; i<N_REGS; i++) begin
            always_ff @(posedge clk_i) begin
                if(rstn_i == 1'b0 ) begin
                    slv_reg[i]<='{default:0};
                end else begin
                    //You could be using ham_mbits_D but code is longer
                    //Some of the ham_mbits_D aren't needed
                    slv_reg[i] <= slv_reg_fte[(i+1)*REG_WIDTH-1:REG_WIDTH*i];
                end
            end
            assign slv_reg_pQ[(i+1)*REG_WIDTH-1:i*REG_WIDTH] = slv_reg[i];
        end
        // pad signals to fill an integer number of 26 bit chunks
        for (genvar i =(N_REGS)*REG_WIDTH; i<N_HAM32_SLV*HAM_D; i++) begin
            assign slv_reg_pQ[i] = 1'b0;
            assign slv_reg_fte[i] = 1'b0;
        end

        //Feed encoded parity bits into extra registers
        for (genvar i =0; i<N_HAM32_SLV; i++) begin
            always_ff @(posedge clk_i) begin
                if(rstn_i == 1'b0 ) begin
                    ham_pbits[(i+1)*HAM_P-1:i*HAM_P]<='{default:0};
                end else begin 
                    ham_pbits[(i+1)*HAM_P-1:i*HAM_P]<={
                                                      ham_mbits_D[i*HAM_M+16]
                                                      ,ham_mbits_D[i*HAM_M+8]
                                                      ,ham_mbits_D[i*HAM_M+4]
                                                      ,ham_mbits_D[i*HAM_M+2]
                                                      ,ham_mbits_D[i*HAM_M+1]
                                                      ,ham_mbits_D[i*HAM_M+0]
                                                     };
                end
            end
            //Get flat registered messages
            assign ham_mbits_Q [(i+1)*HAM_M-1:i*HAM_M] = {
                                                        slv_reg_pQ[i*HAM_D+25:i*HAM_D+11]
                                                        ,ham_pbits[i*HAM_P+5]
                                                        ,slv_reg_pQ[i*HAM_D+10:i*HAM_D+4]
                                                        ,ham_pbits[i*HAM_P+4]
                                                        ,slv_reg_pQ[i*HAM_D+3:i*HAM_D+1]
                                                        ,ham_pbits[i*HAM_P+3]
                                                        ,slv_reg_pQ[i*HAM_D]
                                                        ,ham_pbits[i*HAM_P+2]
                                                        ,ham_pbits[i*HAM_P+1]
                                                        ,ham_pbits[i*HAM_P]
                                                        };
        end
        for (genvar i =0; i<N_HAM32_SLV; i++) begin : slv_ham_dec
            //decoder
            hamming32t26d_dec#(
            )slv_hamming32t26d_dec (
                .data_o(slv_reg_fto[(i+1)*HAM_D-1:i*HAM_D]),
                .hv_i(ham_mbits_Q[(i+1)*HAM_M-1:i*HAM_M]),
                .ded_error_o(ift_slv[i])
            );
        end
        // get a packed 2d structure to assign slv_reg
        for (genvar i =0; i<N_REGS; i++) begin
            assign slv_reg_ufto[i]=slv_reg_fto[(i+1)*REG_WIDTH-1:i*REG_WIDTH];
        end
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
                //Write to slv registers if slave was selected & was a write to a valid register
                //Else register the values given by pmu_raw
                if(address_phase.write_Q && address_phase.select_Q && !invalid_index) begin
                    //Feed and send flat assigment in to original format 
                        //assign flat hamming outputs to slv_reg_Q
                    slv_reg_Q=slv_reg_ufto;
                    slv_reg_Q [slv_index] = dwrite_slave;
                    slv_reg_D = pmu_regs_int;
                    slv_reg_D[slv_index] = dwrite_slave; 
                end else begin
                    slv_reg_D = pmu_regs_int;
                    //Feed and send flat assigment in to original format 
                        //assign flat hamming outputs to slv_reg_Q
                    slv_reg_Q=slv_reg_ufto;
                end
        end 
    end
    endgenerate

//----------------------------------------------
//------------- AHB control logic
//----------------------------------------------
logic [1:0] next;

if (FT==0) begin
    logic [1:0] state;

    //data phase - state update
    always_ff @(posedge clk_i) begin
        if(rstn_i == 1'b0 ) begin
            state <= TRANS_IDLE;
        end else begin 
            state <= next;
        end
    end

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
                if (!address_phase.write_Q && !invalid_index) begin
                    dread_slave = slv_reg_Q[slv_index];
                end else begin
                    dread_slave = 32'hcafe01a1;
                end
            end
            TRANS_SEQUENTIAL:begin
                complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
                dwrite_slave = hwdata_i; 
                if (!address_phase.write_Q && !invalid_index) begin
                    dread_slave = slv_reg_Q[slv_index];
                end else begin
                    dread_slave = 32'hcafee1a1;
                end
            end
        endcase
    end
end else begin : Stateft
    //Fault tolerant implementation
        //Triplication of next and state registers 
    logic [1:0] state_D, state_Q;
    logic state_fte1, state_fte2; //fault tolerance errors
    
    //error1 signals a corrected error, safe to ignore
    triple_reg#(.IN_WIDTH(2)
    )state_trip(
    .clk_i(clk_i),
    .rstn_i(rstn_i),
    .din_i(state_D),
    .dout_o(state_Q),
    .error1_o(state_fte1),
    .error2_o(state_fte2)
    );
    
    //data phase - state update
    always_comb begin
        if(rstn_i == 1'b0 ) begin
            state_D = TRANS_IDLE;
        end else begin 
            state_D = next;
        end
    end

    always_comb begin
    //NOTE: I don't expect any of the cafe beaf values in the registers if they do
    //there is a bug
        case (state_Q)
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
                if (!address_phase.write_Q && !invalid_index) begin
                    dread_slave = slv_reg_Q[slv_index];
                end else begin
                    dread_slave = 32'hcafe01a1;
                end
            end
            TRANS_SEQUENTIAL:begin
                complete_transfer_status = TRANSFER_SUCCESS_COMPLETE; 
                dwrite_slave = hwdata_i; 
                if (!address_phase.write_Q && !invalid_index) begin
                    dread_slave = slv_reg_Q[slv_index];
                end else begin
                    dread_slave = 32'hcafee1a1;
                end
            end
        endcase
    end
end
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
always_comb begin
    case (next) 
        TRANS_IDLE:begin
            address_phase.select_D = hsel_i;
            address_phase.write_D = 0; 
            address_phase.master_addr_D = address_phase.master_addr_Q;
        end
        TRANS_BUSY:begin
            address_phase.select_D = hsel_i;
            address_phase.write_D = 0;
            address_phase.master_addr_D = address_phase.master_addr_Q;
        end
        TRANS_NONSEQUENTIAL:begin
            address_phase.select_D = hsel_i;
            address_phase.write_D = hwrite_i;
            address_phase.master_addr_D = haddr_i;
        end
        TRANS_SEQUENTIAL:begin
            address_phase.select_D = hsel_i;
            address_phase.write_D = hwrite_i;
            address_phase.master_addr_D = haddr_i;
        end
    endcase
end


//data phase - slave response
assign slv_index = address_phase.master_addr_Q[$clog2(N_REGS)+1:2];
assign invalid_index = address_phase.master_addr_Q[$clog2(N_REGS)+1:2] >= N_REGS? 1'b1:1'b0;
assign hrdata_o = dread_slave;

assign hreadyo_o = complete_transfer_status [0];
//TODO: review the amount of bits for hresp_o
assign hresp_o = {{complete_transfer_status[1]},{complete_transfer_status[1]}};

//----------------------------------------------
//------------- PMU_raw instance
//----------------------------------------------
    wire ahb_write_req;
    assign ahb_write_req = address_phase.write_Q && address_phase.select_Q;
    logic pmu_raw_FT1, pmu_raw_FT2;
    
    PMU_raw #(
		.REG_WIDTH(REG_WIDTH),
        .MCCU_N_CORES(MCCU_N_CORES),
		.N_COUNTERS(PMU_COUNTERS),
		.N_SOC_EV(N_SOC_EV),
        .FT(FT),
		.N_CONF_REGS(PMU_CFG)
	)inst_pmu_raw (
		.clk_i(clk_i),
		.rstn_i(rstn_i),
        .regs_i(slv_reg_Q),
        .regs_o(pmu_regs_int),
        .wrapper_we_i(ahb_write_req),
        .intr_FT1_o(pmu_raw_FT1),
        .intr_FT2_o(pmu_raw_FT2),
        //on pourpose .name connections
        .events_i,
        .intr_overflow_o,
        .intr_quota_o,
        .intr_MCCU_o,
        .intr_RDC_o
	);

//----------------------------------------------
//------------- Generate intr_FT_o
//----------------------------------------------
if (FT == 0 ) begin
        assign intr_FT1_o = 1'b0;
        assign intr_FT2_o = 1'b0;
end else begin 
        //Gather all the signals of corrected errors from FT scopes
            // Codestyle. All scopes start with a capital letter
        assign intr_FT1_o = |{Apft.write_fte1,Apft.select_fte1, Apft.master_addr_fte1,
                             Stateft.state_fte1,
                             pmu_raw_FT1
                             };
        //Gather all the signals of uncorrected errors from FT scopes
            // Codestyle. All scopes start with a capital letter
        assign intr_FT2_o = |{Slvft.ift_slv,
                             Apft.write_fte2,Apft.select_fte2, Apft.master_addr_fte2,
                             Stateft.state_fte2,
                             pmu_raw_FT2
                             };
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

    // If there is no write and no reset the slv_Regs used by the counters can
    // only decrease due to an overflow
        //posible resets of counters
    sequence no_counter_reset;
        f_past_valid && ($past(rstn_i) != 0) && (slv_reg[0][1] == 0);
    endsequence
    sequence counter_reset;
        (rstn_i == 0) || (slv_reg[0][1] == 1);
    endsequence
        //There is no pending write or it is not valid
    sequence no_ahb_write;
        //since ahb is pipelined i check for the last addres phase
        f_past_valid && (ahb_write_req==1'b0); 
    endsequence
        //Register 1, assigned to counter 0 can't decrease
    sequence no_decrease_counter(n);
        (slv_reg[n+1] >= $past(slv_reg[n+1])) && f_past_valid;
    endsequence
        //Register 1, can decrease at overflow
    sequence overflow_counter(n);
        $past(slv_reg[n+1]) == 32'hffffffff;
    endsequence
        //check property for all pmu registers.
        //TODO: Do we actually want to check all ? Takes 6 minutes each. 
    generate
        genvar i;
        for (i=0;i<PMU_COUNTERS;i++) begin
        assert property (
            no_ahb_write and (rstn_i==1) and (slv_reg[0][1] == 0)
            |=> no_decrease_counter(i) or overflow_counter(i)
            );
        end
    endgenerate

    //Base configuration register remains stables if last cycle isn't a reset or
    //write
    assert property (
        (ahb_write_req==1'b0) and (rstn_i==1)
        |=> $stable(slv_reg[0]) 
        );
    
    //TODO: If counters cant decrease by their own what explains that we read
    //incoherent values out of the pmu? AHB properties? Does it fail to read
    //when only one core is available? Does only happen in multicore? What if 
    //nops are inserted after each read? 
    

`endif

endmodule
`default_nettype wire //allow compatibility with legacy code and xilinx ip

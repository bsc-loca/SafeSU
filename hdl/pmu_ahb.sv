/*   -- Instance of pmu_ahb.sv                                                     
   component pmu_ahb                                                             
     generic (                                                                   
         haddr  : integer := 0;                                                  
         hmask  : integer := 16#fff#);                                           
         n_regs : integer := 20 ;                                                
         reg_width : integer := CFG_AHBDW --32                                   
     port (                                                                      
         rst   : in  std_ulogic;                                                 
         clk   : in  std_ulogic;                                                 
         -- AHB bus slave interface                                              
         hsel_i       : in  std_ulogic;                               -- slave select
         haddr_i      : in  std_logic_vector(31 downto 0);            -- address bus 
         hwrite_i     : in  std_ulogic;                               -- read/write 
         htrans_i     : in  std_logic_vector(1 downto 0);             -- transfer type
         hsize_i      : in  std_logic_vector(2 downto 0);             -- transfer size
         hburst_i     : in  std_logic_vector(2 downto 0);             -- burst type
         hwdata_i     : in  std_logic_vector(CFG_AHBDW-1 downto 0);   -- write data bus
         hprot_i      : in  std_logic_vector(3 downto 0);             -- prtection control
         hreadyi_i    : in  std_ulogic;                               -- transfer done 
         hmaster_i    : in  std_logic_vector(3 downto 0);             -- current master
         hmastlock_i  : in  std_ulogic;                               -- locked access 
         hreadyo_o    : out std_ulogic;                               -- trasfer done 
         hresp_o      : out std_logic_vector(1 downto 0);             -- response type
         hrdata_o     : out std_logic_vector(CFG_AHBDW-1 downto 0);   -- read data bus
         hsplit_o     : out std_logic_vector(15 downto 0)             -- split completion
         -- PMU input signals                                                    
         -- PMU output signals                                                   
   end component;                                                                
*/


//-----------------------------------------------------
// ProjectName: LEON3_kc705_pmu
// Function   : Integrate PMU and AHB interface
// Description: AHB interface implementation of the  PMU. 
//              
//              This module is responsible managing reads and writes from and
//              AHB master and interface with pmu_ahb module.
//
// Coder      : G.Cabo
// References : AHB5 specifications 
//              https://silver.arm.com/download/download.tm?pv=2646779

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
		// Total amount of registers
        parameter integer N_REGS = 20,                                                
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
    //     -- PMU input signals                                                    
    //     -- PMU output signals                                                   
	);
//----------------------------------------------
//------------- Local parameters
//----------------------------------------------

//----------------------------------------------
//------------- AHB registers
//----------------------------------------------
    reg  [REG_WIDTH-1:0] slv_reg [0:N_REGS-1];
    wire [REG_WIDTH-1:0] slv_reg_D [0:N_REGS-1];
    wire [REG_WIDTH-1:0] slv_reg_Q [0:N_REGS-1];
    
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
    //basic transfers
    //Addres phase 1 cycle unless extended by previous bus transfer
    //Data phase 1 + extende by HREADY
    
    //Simple transfer NO WAIT STATES (1 cycle address + 1 cycle data)
        
        //capture Addres - hold address for data phase
    reg [HADDR_WIDTH-1:0] haddr_int;
    always_ff @(posedge clk_i, negedge rstn_i) begin
        if(rstn_i == 1'b0 ) begin
            haddr_int <= {HADDR_WIDTH{1'b0}};
        end else begin
            haddr_int <= haddr_i;
        end
    end
        //capture data - hold data for data phase
    reg [HDATA_WIDTH-1:0] hdata_int;
    always_ff @(posedge clk_i, negedge rstn_i) begin
        if(rstn_i == 1'b0 ) begin
            hdata_int <= {HDATA_WIDTH{1'b0}};
        end else begin
            hdata_int <= hwdata_i;
        end
    end
        // Detect direction, and register for data stage . HWRITE controls direction
        //(HIGH means write transfer from master to slave)
        //(LOW means read transfer from slave to master)
    wire write_req_d;
    wire read_req_d;
    assign write_req_d = !hreadyi_i? 1'b0 : hwrite_i ? 1'b1 : 1'b0;
    assign read_req_d  = !hreadyi_i? 1'b0 : hwrite_i ? 1'b0 : 1'b1;
    
    reg write_req_q;
    reg read_req_q;
    always_ff @(posedge clk_i, negedge rstn_i) begin
        if(rstn_i == 1'b0 ) begin
            write_req_q <= 1'b0;
            read_req_q <= 1'b0;
        end else begin
            write_req_q <= write_req_d;
            read_req_q <= read_req_d;
        end
    end
    
    // Generate index of write/read responses
        // Assume only 32b acces are done. 2 LSB are not used in address
    wire [$clog2(N_REGS)-1:0] slv_index;
    assign slv_index = haddr_int[$clog2(N_REGS)+1:2];
    
    //Response in data cycle
    reg [REG_WIDTH-1:0] resp_data;
    always_ff @(posedge clk_i, negedge rstn_i) begin
        if(rstn_i == 1'b0 ) begin
            resp_data <= {REG_WIDTH{1'b0}};
        end else begin
            resp_data <= slv_reg[haddr_i];
        end
    end
    //Write in data cycle - Writes to slave registers are arbitrated due to
        //the implementation of my slave
    wire [REG_WIDTH-1:0] write_data;
    assign write_data = hwdata_i; 

    //Send registerd signals to interface
    assign hrdata_o = resp_data; 

    //TODO: If the slave can block the requests move it kto
        //AHB to PMU_raw synchronization section
    //Acknowledge AHB read/write is done
    assign hreadyo_o = write_req_q || read_req_q; 

//TODO report error if reading out of range

//----------------------------------------------
//------------- AHB to PMU_raw synchronization 
//----------------------------------------------
    //This will increase in complexity later
    
    //Write in data cycle
    genvar i;
    generate
        for(i=0;i<N_REGS;i++) begin
            // Always update the next value for the slave registers
            // Careful, remeber to not write when rstn_i is LOW
            assign slv_reg_D[i] = write_req_d && (i==slv_index)
                                ? write_data :slv_reg_Q[i];
        end
    endgenerate   
//----------------------------------------------
//------------- PMU_raw instance
//----------------------------------------------

///////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
    //AHB read and write can't happen at the same time
    always_ff @(posedge clk_i, negedge rstn_i) begin
        assert 1'b1 != (write_req_d && read_req_d) 
        assert 1'b1 != (write_req_q && read_req_q) 
    end
`endif

endmodule

`default_nettype wire //allow compatibility with legacy code and xilinx ip



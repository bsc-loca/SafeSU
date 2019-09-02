# Hierarchy
+ AXI_PMU.sv
    + AXI_PMU_interface_v1_0_S00_AXI.sv
        + MCCU.sv
# Parameters
### AXI_PMU.sv
| Name                     | Defaults | Valid values | Description                                                                              |
|--------------------------|----------|--------------|------------------------------------------------------------------------------------------|
| C_S_AXI_DATA_WIDTH       | 32       | 32/64        | Sets the data width of the bus                                                           |
| C_S_AXI_ADDR_WIDTH       | 7        | integer      | Defines the bits needed by the peripheral to addres internal registers                   |

### AXI_PMU_interface_v1_0_S00_AXI.sv
| Name                     | Defaults | Valid values | Description                                                                              |
|--------------------------|----------|--------------|------------------------------------------------------------------------------------------|
| C_S_AXI_DATA_WIDTH       | 32       | 32/64        | Sets the data width of the bus                                                           |
| C_S_AXI_ADDR_WIDTH       | 7        | integer      | Defines the bits needed by the peripheral to addres internal registers                   |
| N_COUNTERS               | 9        | integer      | Configures the amount of counters and input signals of the unit                          |
| N_CONF_REGS              | 1        | integer      | Sets the amount of configuration registers that are acessible by internal hardware       |
| OVERFLOW                 | 1        | bool         | Instantiates the hardware required to detect overflows and trigger an overflow interrupt |
| QUOTA                    | 1        | bool         | Instantiates the hardware for quota monitoring and quota interrupt                       |
| MCCU                     | 1        | bool         | MCCU - Maximum-contention Control Unit mode                                              |
| N_CORES                  | 1        | integer[1-4] | MCCU - Number of cores to track                                                          |

### MCCU.sv
| Name                     | Defaults | Valid values | Description                                                                              |
|--------------------------|----------|--------------|------------------------------------------------------------------------------------------|
| DATA_WIDTH       | 32       | 32/64         | Width of data registers         |
| WEIGHTS_WIDTH    | 7        | integer       | Width of weights registers      |
| N_CORES          | 4        | integer[1-4]  | MCCU - Number of cores to track |
| CORE_EVENTS      | 4        | integer[1-16] | Signals per core       |
| OVERFLOW_PROT    | DATA_WIDTH * 2| integer | Size of accumulation registers|
| O_D_0PAD      | OVERFLOW_PROT - DATA_WIDTH) | Padding of 0s for overflow and data|
| D_W_0PAD      | DATA_WIDTH - WEIGHTS_WIDTH) | Padding of 0s for weights and data|
| O_W_0PAD      | OVERFLOW_PROT - WEIGHTS_WIDTH| Padding of 0s for  overflow and weights|

# Pinout
### AXI_PMU.sv
| Number | Name          | Type | Bus_wide(bits)   |
|--------|---------------|------|------------------|
| 1      | int_quota_c0_o| out  | 1       |
| 2      | int_quota_c1_o| out  | 1       |
| 3      | int_overflow_o| out  | 1       |
| 4      | int_quota_o     | out  | 1                |
| 5      | EV0_i        | in   | 1      |
| 6      | EV1_i        | in   | 1      |
| 7      | EV2_i        | in   | 1      |
| 8      | EV3_i        | in   | 1      |
| 9      | EV4_i        | in   | 1      |
| 10      | EV5_i        | in   | 1      |
| 11      | EV6_i        | in   | 1      |
| 12      | EV7_i        | in   | 1      |
| 13      | EV8_i        | in   | 1      |
| 14     | EV9_i        | in   | 1      |
| 15     | EV10_i        | in   | 1      |
| 16     | EV11_i        | in   | 1      |
| 17     | EV12_i        | in   | 1      |
| 18     | EV13_i        | in   | 1      |
| 19     | EV14_i        | in   | 1      |
| 20     | EV15_i        | in   | 1      |
| 21      | S_AXI_ACLK_i    | in   | C_S_AXI_DATA_WIDTH |
| 22      | S_AXI_ARESETN_i | in   | C_S_AXI_DATA_WIDTH |
| 23      | S_AXI_AWADDR_i  | in   | C_S_AXI_DATA_WIDTH |
| 24      | S_AXI_AWVALID_i | in   | C_S_AXI_DATA_WIDTH |
| 25     | S_AXI_AWREADY_o | out  | C_S_AXI_DATA_WIDTH |
| 26     | S_AXI_WDATA_i   | in   | C_S_AXI_DATA_WIDTH |
| 27     | S_AXI_WSTRB_i   | in   | C_S_AXI_DATA_WIDTH |
| 28     | S_AXI_WVALID_i  | in   | C_S_AXI_DATA_WIDTH |
| 29     | S_AXI_WREADY_o  | out  | C_S_AXI_DATA_WIDTH |
| 30     | S_AXI_BRESP_o   | out  | C_S_AXI_DATA_WIDTH |
| 31     | S_AXI_BVALID_o  | out  | C_S_AXI_DATA_WIDTH |
| 32     | S_AXI_BREADY_i  | in   | C_S_AXI_DATA_WIDTH |
| 33     | S_AXI_ARADDR_i  | in   | C_S_AXI_DATA_WIDTH |
| 34     | S_AXI_ARVALID_i | in   | C_S_AXI_DATA_WIDTH |
| 35     | S_AXI_ARREADY_o | out  | C_S_AXI_DATA_WIDTH |
| 36     | S_AXI_RDATA_o   | out  | C_S_AXI_DATA_WIDTH |
| 37     | S_AXI_RRESP_o   | out  | C_S_AXI_DATA_WIDTH |
| 38     | S_AXI_RVALID_o  | out  | C_S_AXI_DATA_WIDTH |
| 39     | S_AXI_RREADY_i  | in   | C_S_AXI_DATA_WIDTH |
	
### AXI_PMU_interface_v1_0_S00_AXI.sv
| Number | Name          | Type | Bus_wide(bits)   |
|--------|---------------|------|------------------|
| 1      | MCCU_int_o    | out  | N_CORES       |
| 2      | int_overflow_o| out  | 1       |
| 3      | int_quota_o     | out  | 1                |
| 4      | events_i        | in   | N_COUNTERS       |
| 5      | S_AXI_ACLK_i    | in   | C_S_AXI_DATA_WIDTH |
| 6      | S_AXI_ARESETN_i | in   | C_S_AXI_DATA_WIDTH |
| 7      | S_AXI_AWADDR_i  | in   | C_S_AXI_DATA_WIDTH |
| 8      | S_AXI_AWPROT_i  | in   | C_S_AXI_DATA_WIDTH |
| 9      | S_AXI_AWVALID_i | in   | C_S_AXI_DATA_WIDTH |
| 10     | S_AXI_AWREADY_o | out  | C_S_AXI_DATA_WIDTH |
| 11     | S_AXI_WDATA_i   | in   | C_S_AXI_DATA_WIDTH |
| 12     | S_AXI_WSTRB_i   | in   | C_S_AXI_DATA_WIDTH |
| 13     | S_AXI_WVALID_i  | in   | C_S_AXI_DATA_WIDTH |
| 14     | S_AXI_WREADY_o  | out  | C_S_AXI_DATA_WIDTH |
| 15     | S_AXI_BRESP_o   | out  | C_S_AXI_DATA_WIDTH |
| 16     | S_AXI_BVALID_o  | out  | C_S_AXI_DATA_WIDTH |
| 17     | S_AXI_BREADY_i  | in   | C_S_AXI_DATA_WIDTH |
| 18     | S_AXI_ARADDR_i  | in   | C_S_AXI_DATA_WIDTH |
| 19     | S_AXI_ARPROT_i  | in   | C_S_AXI_DATA_WIDTH |
| 20     | S_AXI_ARVALID_i | in   | C_S_AXI_DATA_WIDTH |
| 21     | S_AXI_ARREADY_o | out  | C_S_AXI_DATA_WIDTH |
| 22     | S_AXI_RDATA_o   | out  | C_S_AXI_DATA_WIDTH |
| 23     | S_AXI_RRESP_o   | out  | C_S_AXI_DATA_WIDTH |
| 24     | S_AXI_RVALID_o  | out  | C_S_AXI_DATA_WIDTH |
| 25     | S_AXI_RREADY_i  | in   | C_S_AXI_DATA_WIDTH |
### MCCU.sv
| Number | Name                 | Type | width(default) |index   |
|--------|---------------       |------|------------------|
| 1      | clk_i                | in   | 1              |       |
| 2      | rst_i                | in   | 1              |      |
| 3      | enable_i             | in   | 1              |     |
| 4      | events_i             | in   | 16 |packed [CORE_EVENTS-1:0] unpacked [0:N_CORES-1] |
| 5      | quota_i              | in   | 128 |packed  [DATA_WIDTH-1:0] unpacked [0:N_CORES-1] |
| 6      | update_quota_i       | in   | 4 |[0:N_CORES-1] |
| 7      | quota_o              | out  | 128 |packed  [DATA_WIDTH-1:0]  unpacked [0:N_CORES-1] |
| 8      | events_weights_i     | in   | 112 |packed  [WEIGHTS_WIDTH-1:0]  unpacked [0:N_CORES-1][0:CORE_EVENTS-1] |
| 9      | interruption_quota_o | out  | 4 |[N_CORES-1:0] |


===========================================================================================================

# Memory map
### MCCU.sv
Pass down to AXI_PMU_interface_v1_0_S00_AXI.sv
### AXI_PMU_interface_v1_0_S00_AXI.sv
| Memory offset (HEX)   | Register  | Name      | Function  | 
| :---:                 |    :----: | :---:     | :---:|
| 0                     | 0         | Cnt\_0    | Contains total of events have been generated by EV0 since last reset|
| ...                   | ...       | ...       | ... |
| 0x3C                  | 15        | Cnt\_15    | Contains total of events have been generated by EV15 since last reset|
| 0x40 | 16 | main\_cfg | control over software reset and enable |
| 0x44  | 17 | aux\_cfg\_0 | Configuration for future features| 
| ...                   | ...       | ...       | ... |
| 0x50  | 20 | aux\_cfg\_3 | Configuration for future features |
| 0x54 | 21 | Overflow | Overflow flags of each counter|
| 0x58 | 22 | Quota\_mask | User defined mask that selects which signals must be acounted for the quota|
| 0x5E | 23 | Quota\_limit | User defined value. When quota is over this value int\_quota is triggered |

### AXI_PMU.sv





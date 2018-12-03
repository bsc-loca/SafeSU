//testbench for the default case where bus is 64bits
#include "VAXI_PMU.h"
#include "VAXI_PMU_AXI_PMU.h"
#include "VAXI_PMU_AXI_PMU_interface_v1_0_S00_AXI__pi1.h"
#include "verilated.h"
//waveform
#include "verilated_vcd_c.h"

#define TRACE_DEF true 

//time for waveforms
vluint64_t main_time =0;//current simulation time
double sc_time_stamp(){ //called by $time in verilog
    return main_time;   //converts to double , to match
}
// debug function to generate waveforms and clock
// debug function to generate waveforms and clock
void ticktoc_and_trace(VAXI_PMU* module,VerilatedVcdC* tfp){
  //waveforms and tick clock
  if (tfp != NULL){
  module->s00_axi_aclk = !module->s00_axi_aclk;
  module->eval();
    tfp->dump (main_time);
    main_time++;
  module->s00_axi_aclk = !module->s00_axi_aclk;
  module->eval();
    tfp->dump (main_time);
    main_time++;
  }else{
  module->s00_axi_aclk = !module->s00_axi_aclk;
  module->eval();
  module->s00_axi_aclk = !module->s00_axi_aclk;
  module->eval();
  }
}
void tick_and_trace(VAXI_PMU* module,VerilatedVcdC* tfp){
  //waveforms and tick clock
  if (tfp != NULL){
  module->s00_axi_aclk = !module->s00_axi_aclk;
  module->eval();
    tfp->dump (main_time);
    main_time++;
  }else{
  module->s00_axi_aclk = !module->s00_axi_aclk;
  module->eval();
  }
}



struct TestCase {
    const char* name;
    
    bool en, clr;
    uint8_t sel_buffer;
    uint8_t sel_events;
  
    //bool s00_axi_aclk,CPUtimer,DcacheMisses;
    uint64_t expected_events;
    uint64_t expected_EV0;
};

TestCase test_cases[] {
//name                        en  clr sel_buffer  sel_events  exNev  exEV0    
  { "slv_reg0"                ,1  ,0  ,0x00       ,0          ,0x0f  ,0x0f  },
  { "slv_reg1"                ,1  ,0  ,0x01       ,0          ,0x0f  ,0x0f },
  { "slv_reg2"                ,1  ,0  ,0x02       ,0          ,0x0f  ,0x0f },
  { "slv_reg3"                ,1  ,0  ,0x03       ,0          ,0x0f  ,0x0f },
  { "slv_reg4"                ,1  ,0  ,0x04       ,0          ,0x0f  ,0x0f },
  { "slv_reg5"                ,1  ,0  ,0x05       ,0          ,0x0f  ,0x0f },
  { "slv_reg6"                ,1  ,0  ,0x06       ,0          ,0x0f  ,0x0f },
  { "slv_reg7"                ,1  ,0  ,0x07       ,0          ,0x0f  ,0x0f },
  { "slv_reg8"                ,1  ,0  ,0x08       ,0          ,0x0f  ,0x0f },
  { "slv_reg9"                ,1  ,0  ,0x09       ,0          ,0x0f  ,0x0f },
  { "slv_reg10"               ,1  ,0  ,0x0a       ,0          ,0x0f  ,0x0f },
  { "slv_reg11"               ,1  ,0  ,0x0b       ,0          ,0x0f  ,0x0f },
  { "slv_reg12"               ,1  ,0  ,0x0c       ,0          ,0x0f  ,0x0f },
  { "slv_reg13"               ,1  ,0  ,0x0d       ,0          ,0x0f  ,0x0f },
  { "slv_reg14"               ,1  ,0  ,0x0e       ,0          ,0x0f  ,0x0f },
  { "slv_reg15"               ,1  ,0  ,0x0f       ,0          ,0x0f  ,0x0f },
  { "slv_reg0"                ,1  ,1  ,0x0f       ,0          ,0x0f  ,0x0f },
};

int main(int argc, char **argv, char **env) {
  //enable waveforms
  bool vcdTrace= TRACE_DEF;
  VerilatedVcdC* tfp =NULL;
  //declare my module
  Verilated::commandArgs(argc, argv);
  VAXI_PMU* PMU = new VAXI_PMU;
  //enable waveforms
  if(vcdTrace)
  {
    Verilated::traceEverOn(true);
    tfp= new VerilatedVcdC;
    PMU->trace(tfp,99);
    std::string vcdname = argv[0];
    vcdname += ".vcd";
    std::cout << vcdname << std::endl;
    tfp->open(vcdname.c_str());
  }
  //pointers to the values of the register
  /*
  uint64_t* output_regs[16]={
  &PMU->slv_reg0
  };*/
  
  //initial configuration
  PMU->s00_ev0=0;
  PMU->s00_axi_aresetn=0;
  tick_and_trace(PMU,tfp);
  PMU->s00_axi_aresetn=1;
  tick_and_trace(PMU,tfp);
 //loop through test cases 
 int num_test_cases = sizeof(test_cases)/sizeof(TestCase);
 for(int k = 0; k < num_test_cases; k++) {
      TestCase *test_case = &test_cases[k];
      //fill configuration register
      PMU->AXI_PMU->AXI_PMU_inst->slv_reg20=0;
      PMU->AXI_PMU->AXI_PMU_inst->slv_reg20|=test_case->en;
      PMU->AXI_PMU->AXI_PMU_inst->slv_reg20|=(test_case->sel_buffer)<<1;
      PMU->AXI_PMU->AXI_PMU_inst->slv_reg20|=(test_case->sel_events)<<5;
      PMU->AXI_PMU->AXI_PMU_inst->slv_reg20|=(test_case->clr)<<9;
      // run  some cycles
      for(uint64_t i=0;i<test_case->expected_EV0;i++){
       PMU->s00_ev0= !PMU->s00_ev0;
          //waveforms and tick clock
       tick_and_trace(PMU,tfp);
       
       PMU->s00_ev0= !PMU->s00_ev0;
          //waveforms and tick clock
       tick_and_trace(PMU,tfp);
       
      }  
  }
  //waveforms
  if (tfp != NULL){
    tfp->dump (main_time);
    main_time++;
  }
  tfp->close();
  PMU->final();
  delete tfp;
  delete PMU;
exit(0);
}


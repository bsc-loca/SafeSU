//-----------------------------------------------------
// Project Name : DRAC
// Function     : Shows intended behaviour 
// Description  : This TB is not used to debug and veryfy just to show the
//                intended behaviour.
// Coder        : G.Cabo


//testbench  is INCOMPLETE, do  not REUSE
#include "VAXI_PMU.h"
#include "VAXI_PMU_AXI_PMU.h"
#include "VAXI_PMU_AXI_PMU_interface_v1_0_S00_AXI__pi1.h"
#include "verilated.h"
//waveform
#include "verilated_vcd_c.h"
#include <algorithm> 
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
  module->eval();
  module->S_AXI_ACLK_i = !module->S_AXI_ACLK_i;
  module->eval();
  tfp->dump (main_time);
  module->eval();
    main_time++;
  module->eval();
  module->S_AXI_ACLK_i = !module->S_AXI_ACLK_i;
  module->eval();
    tfp->dump (main_time);
  module->eval();
    main_time++;
  module->eval();
  }else{
  module->eval();
  module->S_AXI_ACLK_i = !module->S_AXI_ACLK_i;
  module->eval();
  module->S_AXI_ACLK_i = !module->S_AXI_ACLK_i;
  module->eval();
  }
}
void tick_and_trace(VAXI_PMU* module,VerilatedVcdC* tfp){
  //waveforms and tick clock
  if (tfp != NULL){
  module->eval();
  module->S_AXI_ACLK_i = !module->S_AXI_ACLK_i;
  module->eval();
    tfp->dump (main_time);
  module->eval();
    main_time++;
  module->eval();
  }else{
  module->eval();
  module->S_AXI_ACLK_i = !module->S_AXI_ACLK_i;
  module->eval();
  }
}



struct TestCase {
    const char* name;
    bool en, clr;
    uint64_t ev0,ev1,ev2,ev3,quota_mask,quota_lim;
};

TestCase test_cases[] {
//name                  en,clr,ev0,ev1,ev2,ev3,quota_mask,quota_lim     
  { "No Int_quota "     ,1 ,0  ,2  ,3  ,3  ,4  ,0b11    ,6   },
  { "Int_quota "        ,1 ,0  ,1  ,0  ,0  ,0  ,0b11    ,6   },
  { "Int_quota "        ,1 ,0  ,1  ,3  ,3  ,4  ,0b11    ,6   },
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
  
  //initial reset 
  PMU->S_AXI_ARESETN_i=0;
  ticktoc_and_trace(PMU,tfp);
  PMU->S_AXI_ARESETN_i=1;
  ticktoc_and_trace(PMU,tfp);
 //loop through test cases 
 int num_test_cases = sizeof(test_cases)/sizeof(TestCase);
 for(int k = 0; k < num_test_cases; k++) {
      TestCase *test_case = &test_cases[k];
      //fill configuration register
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[16]|=test_case->en;
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[16]|=(test_case->clr)<<1;
      //set the mask for quota
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[22]|=test_case->quota_mask; 
      //Set the limit of quota
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[23]|=test_case->quota_lim;
      // run  some cycles
      uint64_t tmp=std::max(std::max(test_case->ev0,test_case->ev1),std::max(test_case->ev2,test_case->ev3));
      for(uint64_t i=0;i<tmp;i++){
      tick_and_trace(PMU,tfp);
      tick_and_trace(PMU,tfp);
        if(i<test_case->ev0){
            PMU->EV0_i= 1;
        }
        if(i<test_case->ev1){
            PMU->EV1_i= 1;
        }
        if(i<test_case->ev2){
            PMU->EV2_i= 1;
        }
        if(i<test_case->ev3){
            PMU->EV3_i= 1;
        }
        
        if(i>=test_case->ev0){
            PMU->EV0_i= 0;
        }
        if(i>=test_case->ev1){
            PMU->EV1_i= 0;
        }
        if(i>=test_case->ev2){
            PMU->EV2_i= 0;
        }
        if(i>=test_case->ev3){
            PMU->EV3_i= 0;
        }
      }  
  }
    
  //do a software reset
  PMU->AXI_PMU->inst_AXI_PMU->slv_reg[16]|=1<<1;
  tick_and_trace(PMU,tfp);
  tick_and_trace(PMU,tfp);
  //continue monitoring
  PMU->AXI_PMU->inst_AXI_PMU->slv_reg[16]&=0<<1;
  tick_and_trace(PMU,tfp);
  tick_and_trace(PMU,tfp);
  //delay test
  tick_and_trace(PMU,tfp);
  tick_and_trace(PMU,tfp);
  tick_and_trace(PMU,tfp);
  tick_and_trace(PMU,tfp);
  tick_and_trace(PMU,tfp);
  tick_and_trace(PMU,tfp);
  tick_and_trace(PMU,tfp);
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



//-----------------------------------------------------
// ProjectName: MCCU research 
// Function   : Shows intended behaviour 
// Description: This TB is not used to debug and veryfy just to show the
//              intended behaviour.
// Coder        : G.Cabo


#include "VMCCU.h"
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
void ticktoc_and_trace(VMCCU* module,VerilatedVcdC* tfp){
  //waveforms and tick clock
  if (tfp != NULL){
  module->eval();
  module->clk_i = !module->clk_i;
  module->eval();
  tfp->dump (main_time);
  module->eval();
    main_time++;
  module->eval();
  module->clk_i = !module->clk_i;
  module->eval();
    tfp->dump (main_time);
  module->eval();
    main_time++;
  module->eval();
  }else{
  module->eval();
  module->clk_i = !module->clk_i;
  module->eval();
  module->clk_i = !module->clk_i;
  module->eval();
  }
}
void tick_and_trace(VMCCU* module,VerilatedVcdC* tfp){
  //waveforms and tick clock
  if (tfp != NULL){
  module->eval();
  module->clk_i = !module->clk_i;
  module->eval();
    tfp->dump (main_time);
  module->eval();
    main_time++;
  module->eval();
  }else{
  module->eval();
  module->clk_i = !module->clk_i;
  module->eval();
  }
}



struct TestCase {
    const char* name;
    bool en, rstn;
};

TestCase test_cases[] {
//name                  en,clr,ev0,ev1,ev2,ev3,quota_mask,quota_lim     
  { "No Int_quota "     ,1 ,0  },
};

int main(int argc, char **argv, char **env) {
  //enable waveforms
  bool vcdTrace= TRACE_DEF;
  VerilatedVcdC* tfp =NULL;
  //declare my module
  Verilated::commandArgs(argc, argv);
  VMCCU* MCCU = new VMCCU;
  //enable waveforms
  if(vcdTrace)
  {
    Verilated::traceEverOn(true);
    tfp= new VerilatedVcdC;
    MCCU->trace(tfp,99);
    std::string vcdname = argv[0];
    vcdname += ".vcd";
    std::cout << vcdname << std::endl;
    tfp->open(vcdname.c_str());
  }
  
  //initial reset 
  MCCU->rstn_i=0;
  ticktoc_and_trace(MCCU,tfp);
  MCCU->rstn_i=1;
  ticktoc_and_trace(MCCU,tfp);
 //loop through test cases 
 int num_test_cases = sizeof(test_cases)/sizeof(TestCase);
 for(int k = 0; k < num_test_cases; k++) {
      TestCase *test_case = &test_cases[k];
  }
    
  //delay test
  tick_and_trace(MCCU,tfp);
  tick_and_trace(MCCU,tfp);
  tick_and_trace(MCCU,tfp);
  tick_and_trace(MCCU,tfp);
  tick_and_trace(MCCU,tfp);
  tick_and_trace(MCCU,tfp);
  tick_and_trace(MCCU,tfp);
  //waveforms
  if (tfp != NULL){
    tfp->dump (main_time);
    main_time++;
  }
  tfp->close();
  MCCU->final();
  delete tfp;
  delete MCCU;
exit(0);
}



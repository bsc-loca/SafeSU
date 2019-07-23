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
    bool rstn_i, enable_i; 
    uint64_t events_i[4]; 
    uint64_t quota_i[4]; 
    uint16_t events_weights_i[4][4];
};

TestCase test_cases[] {
//name                  ,rstn_i ,enable_i ,events_i      ,quota_i    ,events_weights_i 
  { "Rst          "     ,0      ,0        ,{0,2,0,4}     ,{0,0,0,0} ,{{0,0,0,0},{5,0,0,8},{9,0,11,7},{9,6,11,11}}},
  { "Init         "     ,1      ,0        ,{15,15,7,7}   ,{10,15,20,25} ,{{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16}}},
  { "Delay        "     ,1      ,0        ,{15,15,3,4}   ,{10,15,20,25} ,{{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16}}},
  { "Enable       "     ,1      ,1        ,{13,12,3,4}   ,{10,15,20,25} ,{{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16}}},
  { "Enable       "     ,1      ,1        ,{1,2,3,4}     ,{10,15,20,25} ,{{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16}}},
};
/*
TestCase test_cases[] {
//name                  ,rstn_i ,enable_i ,events_i      ,quota_i    ,events_weights_i 
  { "Rst          "     ,0      ,0        ,{0,0,0,0}     ,{0,0,0,0} ,{{0,0,0,0},{0,0,0,0},{9,0,11,7},{9,6,11,11}}},
  { "Init         "     ,1      ,0        ,{1,0,0,0}   ,{0,0,0,0} ,{{512,0,0,0},{0,0,0,0},{9,10,11,12},{13,14,15,16}}},
  { "wait          "    ,1      ,0        ,{0,0,0,0}     ,{0,0,0,0} ,{{0,0,0,0},{0,0,0,0},{9,0,11,7},{9,6,11,11}}},
};*/

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
      MCCU->rstn_i = test_case->rstn_i;
      MCCU->enable_i = test_case->enable_i;
    //TODO: find a way to read localparam to  drive this loops
      int N_CORES =2; 
      int CORE_EVENTS=4;
      for( int i = 0; i<N_CORES; i++){
          MCCU->events_i[i] = test_case->events_i[i];
          MCCU->quota_i[i] = test_case->quota_i[i];
          for(int j = 0; j<CORE_EVENTS; j++) {
            MCCU->events_weights_i[i][j] = test_case->events_weights_i[i][j];
          }
      }
      ticktoc_and_trace(MCCU,tfp);
//  printf("%s: passed\n", MCCU->DATA_WIDTH);
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



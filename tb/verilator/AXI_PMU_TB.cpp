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

#define addr_PMU_main_cfg 16 
#define addr_PMU_quota_mask 22 
#define addr_PMU_quota_limit 23 
#define addr_MCCU_main_cfg 24 
#define addr_MCCU_c0_available_quota 25 
#define addr_MCCU_c1_available_quota 26 
#define addr_MCCU_weights_r0 27 
#define addr_MCCU_weights_r1 28 

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
    bool en, clr, wren;
    uint32_t ev0,ev1,ev2,ev3,quota_mask,quota_lim, MCCU_cfg,MCCU_c0_av_quota,MCCU_c1_av_quota,MCCU_weight0,MCCU_weight1;
};
	//assign slv_reg_wren = axi_wready && S_AXI_WVALID_i && axi_awready && S_AXI_AWVALID_i;

TestCase test_cases[] {
//name                  en,clr,wren,ev0,ev1,ev2,ev3,quota_mask,quota_lim,MCCU_cfg,MCCU_c0_av_quota,MCCU_c1_av_quota,MCCU_weight0,MCCU_weight1    
  { "No Int_quota "     ,1 ,0 ,1 ,2  ,3  ,3  ,4  ,0b11      ,6       ,0      ,0               ,0               ,0           ,0   },
  { "Int_quota "        ,1 ,0 ,1 ,1  ,0  ,0  ,0  ,0b11      ,6       ,0      ,0               ,0               ,0           ,0   },
  { "Int_quota "        ,1 ,0 ,1 ,1  ,3  ,3  ,4  ,0b11      ,6       ,0      ,0               ,0               ,0           ,0   },
  { "Set_MCCU  "        ,1 ,0 ,1 ,0  ,0  ,0  ,0  ,0b00      ,0       ,0      ,15              ,0               ,0           ,0},
  { "Set_MCCU  "        ,1 ,0 ,1 ,0  ,0  ,0  ,0  ,0b00      ,0       ,0      ,15              ,10              ,0           ,0},
  { "Set_MCCU  "        ,1 ,0 ,1 ,0  ,0  ,0  ,0  ,0b00      ,0       ,0      ,15              ,10              ,0xffff  ,0},
  { "Set_MCCU  "        ,1 ,0 ,1 ,0  ,0  ,0  ,0  ,0b00      ,0       ,0      ,15              ,10              ,0xffff  ,0xffff },
  { "Set_MCCU  "        ,1 ,0 ,1 ,0  ,0  ,0  ,0  ,0b00      ,0       ,0xffff ,15              ,10              ,0xffff  ,0xffff },
  { "Set_MCCU  "        ,1 ,0 ,0 ,0  ,0  ,0  ,0  ,0b00      ,0       ,0xffff ,15              ,10              ,0xffff  ,0xffff },
  { "Set_MCCU  "        ,1 ,0 ,1 ,0  ,0  ,0  ,0  ,0b00      ,0       ,0x0fff ,15              ,10              ,0xffff  ,0xffff },
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
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_PMU_main_cfg]|=test_case->en;
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_PMU_main_cfg]|=(test_case->clr)<<1;
      //set the mask for quota
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_PMU_quota_mask]|=test_case->quota_mask; 
      //Set the limit of quota
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_PMU_quota_limit]|=test_case->quota_lim;
      //set the MCCU values
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_MCCU_main_cfg]=test_case->MCCU_cfg; 
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_MCCU_c0_available_quota]=test_case->MCCU_c0_av_quota; 
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_MCCU_c1_available_quota]=test_case->MCCU_c1_av_quota; 
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_MCCU_weights_r0]=test_case->MCCU_weight0; 
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_MCCU_weights_r1]=test_case->MCCU_weight1; 
      PMU->AXI_PMU->inst_AXI_PMU->slv_reg_wren=1; 
      // run  some cycles
      uint64_t tmp=std::max(std::max(test_case->ev0,test_case->ev1),std::max(test_case->ev2,test_case->ev3));
      //if no events, still execute one cycle
      if(tmp==0)
        tmp=1;
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
  //force overflow
  PMU->AXI_PMU->inst_AXI_PMU->slv_reg[4]=0xfffffffe;
  for(uint64_t i=0;i<3;i++){
    PMU->EV4_i= !PMU->EV4_i;
    //waveforms and tick clock
    tick_and_trace(PMU,tfp);
    //waveforms and tick clock
    PMU->EV4_i= !PMU->EV4_i;
    tick_and_trace(PMU,tfp);
  }  
  //do a software reset
  PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_PMU_main_cfg]|=1<<1;
  tick_and_trace(PMU,tfp);
  tick_and_trace(PMU,tfp);
  //continue monitoring
  PMU->AXI_PMU->inst_AXI_PMU->slv_reg[addr_PMU_main_cfg]&=0<<1;
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
  //do a hard reset
  PMU->S_AXI_ARESETN_i=0;
  ticktoc_and_trace(PMU,tfp);
  PMU->S_AXI_ARESETN_i=1;
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



#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#define IO_BASE (0x80000000)
#define IO_MASK    (0x0002ffff)
#define PMU_BASE (0x80020000)
#define MASK3    (0x050)
#define CONG_REG_1_OFFSET (0x40) //32Bit Counters
//#define CONG_REG_1_OFFSET (0xA0) //64Bit Counters
typedef enum { false, true } bool;


void read_test_loop(uint32_t entry, uint32_t exit,uint32_t aligment){
    volatile uint32_t *var;
    volatile uint32_t reader;
    //printf("\n *** Memory dump***\n\n");
    for(uint32_t i=entry;i<exit+4;i=i+aligment){
        var=(uint32_t*)(i);
        reader=*var;
        //printf("addres:%x \n",i);
        //printf("value :%d \n",reader);
    }
   //printf("\n *** END DUMP ***\n\n");
}
void search_loop(uint32_t entry, uint32_t exit,uint32_t aligment, uint32_t key){
    volatile uint32_t *var;
    volatile uint32_t reader;
    //printf("\n *** Memory dump***\n\n");
    for(uint32_t i=entry;i<exit+4;i=i+aligment){
        var=(uint32_t*)(i);
        reader=*var;
        if (reader==key){
        //printf("addres:%x \n",i);
        //printf("value :%d \n",reader);
            i=exit;
        }

    }
   //printf("\n *** END DUMP ***\n\n");
}

void enable_PMU_32b (void){
    volatile uint32_t *var;
    var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    *var=1;
}

void disable_PMU_32b (void){
    volatile uint32_t *var;
    var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    *var=0;
}

uint32_t reset_pmu(void){
    //reset counters 
    volatile uint32_t *var;
    var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    //var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    *var=2;
}

uint32_t test_pmu(void){
    //enable PMU 
   // read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    //printf("\n ***Reset***\n\n");
    reset_pmu();
   // read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    //printf("\n ***Enable***\n\n");
    enable_PMU_32b();
    read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    reset_pmu();
    //printf("\n ***Disable***\n\n");
  //  disable_PMU_32b ();
   // read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    return(0);
}
void main(void){
    //read_test_loop(PMU_BASE,PMU_BASE+0x01fff,4);
    //printf("\n ***TEST***\n\n");
    //while(1){
    test_pmu();
    //search_loop(IO_BASE,PMU_BASE+IO_MASK,4,0xDEAD);
}

#include "PMU.h"
//#define CONG_REG_1_OFFSET (0xA0) //64Bit Counters
typedef enum { false, true } bool;

#define CYCLES 0
#define IMISS 1
#define ITLBMISS 2
#define DMISS 3
#define DTLBMISS 4
#define STORES 5
#define LOAD 6
#define BRANCH 7
#define INSTR 8


void read_test_loop(uint32_t entry, uint32_t exit,uint32_t aligment){
    volatile uint32_t *var;
    volatile uint32_t reader;
    #ifdef __UART__
    printf("\n *** Memory dump***\n\n");
    #endif
    for(uint32_t i=entry;i<exit+4;i=i+aligment){
        var=(uint32_t*)(i);
        reader=*var;
        #ifdef __UART__
        printf("addres:%x \n",i);
        printf("value :%d \n",reader);
        #endif
    }
    #ifdef __UART__
    printf("\n *** END DUMP ***\n\n");
    #endif
}
void search_loop(uint32_t entry, uint32_t exit,uint32_t aligment, uint32_t key){
    volatile uint32_t *var;
    volatile uint32_t reader;
    #ifdef __UART__
    printf("\n *** END DUMP ***\n\n");
    printf("\n *** Memory dump***\n\n");
    #endif
    for(uint32_t i=entry;i<exit+4;i=i+aligment){
        var=(uint32_t*)(i);
        reader=*var;
        if (reader==key){
        #ifdef __UART__
        printf("addres:%x \n",i);
        printf("value :%d \n",reader);
        #endif
            i=exit;
        }

    }
    #ifdef __UART__
    printf("\n *** END DUMP ***\n\n");
    #endif
}

void enable_PMU_32b (void){
    uint32_t *var;
    var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    *var=1;
}

void disable_PMU_32b (void){
    uint32_t *var;
    var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    *var=0;
}

uint32_t get_cycles_32b (void){
    volatile uint32_t *var;
    var=(uint32_t*)(PMU_BASE+CYCLES*4);
    #ifdef __UART__
    printf("CYCLES\n");
    printf("value :%d \n",*var);
    printf("Is the CYCLES counter at address :%x \n",var);
    #endif
    return *var;
}
uint32_t get_instr_32b (void){
    volatile uint32_t *var;
    var=(uint32_t*)(PMU_BASE+INSTR*4);
    #ifdef __UART__
    printf("INSTRUCTIONS\n");
    printf("value :%d \n",*var);
    printf("Is the CYCLES counter at address :%x \n",var);
    #endif
    return *var;
}

uint32_t reset_pmu(void){
    //reset counters 
    volatile uint32_t *var;
    var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    //var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    *var=2;
}

uint32_t get_cycles(void){
    //reset counters 
    volatile uint32_t *var;
    var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    //var=(uint32_t*)(PMU_BASE+CONG_REG_1_OFFSET);
    *var=2;
}

uint32_t test_pmu(void){
    //enable PMU 
    read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    #ifdef __UART__
    printf("\n ***Reset***\n\n");
    #endif
    reset_pmu();
    read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    #ifdef __UART__
    printf("\n ***Enable***\n\n");
    #endif
    enable_PMU_32b();
    read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    #ifdef __UART__
    printf("\n ***Disable***\n\n");
    #endif
    disable_PMU_32b ();
    read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    return(0);
}


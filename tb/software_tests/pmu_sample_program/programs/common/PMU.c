#include <PMU.h>
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
    var=(uint32_t*)(PMU_BASE + MAIN_CONF_REG);
    *var=1;
}

void disable_PMU_32b (void){
    uint32_t *var;
    var=(uint32_t*)(PMU_BASE+MAIN_CONF_REG);
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
    var=(uint32_t*)(PMU_BASE+MAIN_CONF_REG);
    //var=(uint32_t*)(PMU_BASE+MAIN_CONF_REG);
    *var=2;
    return *var;
}

uint32_t get_overflow_32b(void){
    volatile uint32_t *var;
    for(int i=0; i<N_OVERFLOW_REGS;i++){
        var=(uint32_t*)(BASE_OVERFLOW+i*4);
        #ifdef __UART__
        printf("OVERFLOW REG%d\n",i);
        printf("value :%d \n",*var);
        #endif
    }
    return *var;
}
//we write the overflow register to get rid of the interrupt?
uint32_t get_quota_mask_32b(void){
    volatile uint32_t *var;
    for(int i=0; i<N_QUOTA_MASK;i++){
        var=(uint32_t*)(FIRST_QUOTA_MASK+i*4);
        #ifdef __UART__
        printf("QUOTA MASK REG%d\n",i);
        printf("value :%d \n",*var);
        #endif
    }
    return *var;
}

uint32_t set_quota_mask_32b(uint32_t mask[N_QUOTA_MASK]){
    volatile uint32_t *var;
    for(int i=0; i<N_QUOTA_MASK;i++){
        var=(uint32_t*)(FIRST_QUOTA_MASK+i*4);
        *var = mask[i];
    }
    return mask;
}

uint32_t get_quota_limit_32b(void){
    volatile uint32_t *var;
    for(int i=0; i<N_QUOTA_LIMIT;i++){
        var=(uint32_t*)(FIRST_QUOTA_LIMIT+i*4);
        #ifdef __UART__
        printf("QUOTA_LIMIT REG\n");
        printf("value :%d \n",*var);
        #endif
    }
    return *var;
}

uint32_t set_quota_limit_32b(uint32_t limits[N_QUOTA_LIMIT]){
    volatile uint32_t *var;
    for(int i=0; i<N_QUOTA_LIMIT;i++){
        var=(uint32_t*)(FIRST_QUOTA_LIMIT+i*4);
        *var = limits[i];
    }
    return limits;
}
//MCCU functions
uint32_t enable_MCCU_32b(void){
    volatile uint32_t *var;
    var=(uint32_t*)(BASE_MCCU);
    *var = 0x80000000;
    return *var;
}
uint32_t update_registers_MCCU_32b(void){
//note that this function disables MCCU. In order to prevent it you can write
//0xffffffff instead
    volatile uint32_t *var;
    var=(uint32_t*)(BASE_MCCU);
    *var = 0x7fffffff;
    return *var;
}
uint32_t get_main_config_MCCU_32b(void){
    volatile uint32_t *var;
    var=(uint32_t*)(BASE_MCCU);
    #ifdef __UART__
    printf("MCCU main CONFIG REG\n");
    printf("value :%d \n",*var);
    #endif
    return *var;
}
uint32_t get_quota_MCCU_32b(void){
    volatile uint32_t *var;
    for(int i=0; i<N_CORES_MCCU;i++){
        var=(uint32_t*)(FIRST_MCCU_QUOTA+i*4);
        #ifdef __UART__
        printf("MCCU QUOTA_LIMIT REG\n");
        printf("value :%d \n",*var);
        #endif
    }
}
uint32_t set_quota_MCCU_32b(uint32_t quota[MCCU_N_CORES]){
    volatile uint32_t *var;
    for(int i=0; i<MCCU_N_CORES;i++){
        var=(uint32_t*)(FIRST_MCCU_QUOTA+i*4);
        *var = quota[i];
    }
    return quota;
}
uint32_t get_weights_MCCU_32b(void){
    volatile uint32_t *var;
    for(int i=0; i<N_REGS_MCCU_WEIGHTS;i++){
        var=(uint32_t*)(FIRST_MCCU_WEIGHTS+i*4);
        #ifdef __UART__
        printf("QUOTA_LIMIT REG\n");
        printf("value :%d \n",*var);
        #endif
    }
}
uint32_t set_weights_MCCU_32b(uint32_t weights[MCCU_WEIGHTS_REGS]){
    volatile uint32_t *var;
    for(int i=0; i<MCCU_WEIGHTS_REGS;i++){
        var=(uint32_t*)(FIRST_MCCU_WEIGHTS+i*4);
        *var = weights[i];
    }
    return weights;
}
//MCCU quota interrupts are not mapped to registers. How do we read them?


uint32_t test_pmu(void){
//call ALL
enable_PMU_32b ();
disable_PMU_32b ();
get_cycles_32b ();
get_instr_32b ();
reset_pmu();
get_overflow_32b();

uint32_t mask [N_QUOTA_MASK] ={0xffff};
set_quota_mask_32b(mask);
get_quota_mask_32b();

uint32_t limits [N_QUOTA_LIMIT] ={0xaaaa};
set_quota_limit_32b(limits);
get_quota_limit_32b();

get_main_config_MCCU_32b();
uint32_t MCCU_quota [MCCU_N_CORES] ={0xcccc,0xdddd};
set_quota_MCCU_32b(MCCU_quota);
get_quota_MCCU_32b();
uint32_t MCCU_weights [MCCU_WEIGHTS_REGS] ={0xbeefbeef,0xcafecafe};
set_weights_MCCU_32b(MCCU_weights);
get_weights_MCCU_32b();
update_registers_MCCU_32b();//note that this function disables MCCU
enable_MCCU_32b();
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
    get_overflow_32b();
    read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    return(0);
}


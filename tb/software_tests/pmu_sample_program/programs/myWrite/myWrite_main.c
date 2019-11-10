#include "PMU.h"

#include <stdio.h>

#ifdef __UART__
#include "uart.h"
#endif

#include <stdint.h>
#include <stdlib.h>


uint32_t bench_pmu(void){
#ifdef __UART__
    printf("\n ***bench_pmu***\n\n");
#endif
    enable_PMU_32b();
    int a=0, b =0;
    for(int i = 0 ; i< 0xfffff; i++){
        a=i-b;
        if(i%3){
            b++;
        read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
        }
    }
    disable_PMU_32b ();
    read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    return(0);
}
void main(void){
#ifdef __UART__
    uart_init();
#endif
   test_pmu();
}


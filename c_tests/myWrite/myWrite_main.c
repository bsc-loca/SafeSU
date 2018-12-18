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
    search_loop(IO_BASE,IO_BASE+IO_MASK,4,0xBEAF);
    disable_PMU_32b ();
    read_test_loop(PMU_BASE,PMU_BASE+MASK3,4);
    return(0);
}
void main(void){
#ifdef __UART__
    uart_init();
#endif
   // printf("\n ***DELAY***\n\n");
   // read_test_loop(PMU_BASE,PMU_BASE+0x01fff,4);
   // test_pmu();
   bench_pmu();
   //search_loop(IO_BASE,PMU_BASE+IO_MASK,4,0xDEAD);
}


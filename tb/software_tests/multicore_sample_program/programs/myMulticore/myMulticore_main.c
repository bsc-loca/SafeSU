#include "PMU.h"

#include <stdio.h>

#ifdef __UART__
#include "uart.h"
#endif

#include <stdint.h>
#include <stdlib.h>

void contender(void){
#ifdef __UART__
    printf("\n ***load_contender***\n\n");
#endif
read_test_loop(0x4000,PMU_BASE-1,4);

}
void main(void){
#ifdef __UART__
    uart_init();
#endif/*
    uint32_t *var;
    var=(uint32_t*)(0x8002004c);
    *var=1;*/
//enable_PMU_32b();
while(1);
}

void thread_entry(int cid, int nc)
{
  if (cid > 0){
   contender();
//ub_dpath_01_01_02_run(ub_dpath_01_01_02_init());

  }
}

void contender_loop(uint32_t entry, uint32_t exit,uint32_t aligment){
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


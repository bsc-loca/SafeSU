#define _GNU_SOURCE
#include <sched.h>
#include <string.h>
#include <stdio.h>
#include <pthread.h>
#include <unistd.h>
#include <stdlib.h>
#include <errno.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/mman.h>
#include "../../../drivers/linux-driver/linux_safesu_hw.h"
#include "encoding.h"
#include "ubs.h"

#define TEST_ITERS       1000

#define N_CORES         6
#define TUA_CORE_IDX    0

    #define EVENT_COUNT	(14U) //Up to 32

    const crossbar_event_t crossbar_event_table [] = {
    //Multicore test 4-core configuration
    //    {CROSSBAR_OUTPUT_1,     EVENT_0,    "\033[0;34m Constant High (Clock cycles) \033[0m"},
    //    {CROSSBAR_OUTPUT_2,     EVENT_6,    "\033[0;31m Core 0: Data cache miss \033[0m"},
    //    {CROSSBAR_OUTPUT_3,     EVENT_2,    "\033[0;34m Instruction count pipeline 0 \033[0m"},
    //    {CROSSBAR_OUTPUT_4,     EVENT_4,   "\033[0;34m Core 0: Instruction cache miss \033[0m"},
    //    {CROSSBAR_OUTPUT_5,     EVENT_13,   "\033[0;31m Core 1: Data cache miss \033[0m"},
    //    {CROSSBAR_OUTPUT_6,     EVENT_33,   "\033[0;31m Contention caused to core 0 due to core 1 AHB accesses \033[0m"},
    //    {CROSSBAR_OUTPUT_7,     EVENT_20,   "\033[0;31m Core 2: Data cache miss \033[0m"},
    //    {CROSSBAR_OUTPUT_8,     EVENT_36,   "\033[0;31m Contention caused to core 0 due to core 2 AHB accesses \033[0m"},
    //    {CROSSBAR_OUTPUT_9,     EVENT_27,   "\033[0;31m Core 3: Data cache miss \033[0m"},
    //    {CROSSBAR_OUTPUT_10,    EVENT_39,   "\033[0;31m Contention caused to core 0 due to core 3 AHB accesses \033[0m"}
    //Multicore test 6-core configuration
    //
        {CROSSBAR_OUTPUT_1,     EVENT_0,    "\033[0;34m Constant High (Clock cycles) \033[0m"},
        {CROSSBAR_OUTPUT_2,     EVENT_6,    "\033[0;32m Core 0: Data cache miss \033[0m"},
        {CROSSBAR_OUTPUT_3,     EVENT_2,    "\033[0;34m Instruction count Core 0 pipeline 0 \033[0m"},
        {CROSSBAR_OUTPUT_4,     EVENT_4,   "\033[0;34m Core 0: Instruction cache miss \033[0m"},
        {CROSSBAR_OUTPUT_5,     EVENT_13,   "\033[0;32m Core 1: Data cache miss \033[0m"},
        //{CROSSBAR_OUTPUT_5,     EVENT_9,   "\033[0;32m Instruction count Core 1 pipeline 0 \033[0m"},
        {CROSSBAR_OUTPUT_6,     EVENT_49,   "\033[0;33m Contention caused to core 0 due to core 1 AHB accesses \033[0m"},
        {CROSSBAR_OUTPUT_7,     EVENT_20,   "\033[0;32m Core 2: Data cache miss \033[0m"},
        {CROSSBAR_OUTPUT_8,     EVENT_54,   "\033[0;33m Contention caused to core 0 due to core 2 AHB accesses \033[0m"},
        {CROSSBAR_OUTPUT_9,     EVENT_27,   "\033[0;32m Core 3: Data cache miss \033[0m"},
        {CROSSBAR_OUTPUT_10,    EVENT_59,   "\033[0;33m Contention caused to core 0 due to core 3 AHB accesses \033[0m"},
        {CROSSBAR_OUTPUT_11,    EVENT_34,   "\033[0;32m Core 4: Data cache miss \033[0m"},
        {CROSSBAR_OUTPUT_12,    EVENT_64,   "\033[0;33m Contention caused to core 0 due to core 4 AHB accesses \033[0m"},
        {CROSSBAR_OUTPUT_13,    EVENT_41,   "\033[0;32m Core 5: Data cache miss \033[0m"},
        {CROSSBAR_OUTPUT_14,    EVENT_69,   "\033[0;33m Contention caused to core 0 due to core 5 AHB accesses \033[0m"}
    };




int stick_this_thread_to_core(int core_id) {
   int num_cores = sysconf(_SC_NPROCESSORS_ONLN);
   if (core_id < 0 || core_id >= num_cores)
      return EINVAL;

   cpu_set_t cpuset;
   CPU_ZERO(&cpuset);
   CPU_SET(core_id, &cpuset);

   pthread_t current_thread = pthread_self();    
   return pthread_setaffinity_np(current_thread, sizeof(cpu_set_t), &cpuset);
}  

int ub_dataset[100 * 1024 * 1024];

void *analysis_pthread_fn(void *arg) {
    unsigned int core_no = *(unsigned int *)arg;
    stick_this_thread_to_core(core_no);

    setpriority(PRIO_PROCESS, 0, -20);
    
    pmu_counters_disable();
    
    pmu_counters_reset();

    pmu_register_events(crossbar_event_table, EVENT_COUNT);

    printf("----------\n");
    printf("* Before enabling counters:\n");    
    pmu_counters_print(crossbar_event_table, EVENT_COUNT);

    char my_fn[1024 * 1024];
    void (*my_caller)(void *) = (void *)&my_fn[0];

    for(int i=-1; i<ubs_size; ++i) {
        ub_run_t ub;
        printf("==========\n");
        printf("Experiment \"%s\"\n", i>=0?ubs[i].name:"(no ub)");

        pmu_counters_reset();
        pmu_counters_enable();

        if(i>=0) { 
            ub.ub_run_fn = ubs[i].fn;
            
            const unsigned char needle[] = {0x05, 0xca, 0x5c, 0x0b};
            int ret;            
            ub.ub_run_fn_bytes_len = memmem(ub.ub_run_fn, 10 * 1024, needle, sizeof(needle)/sizeof(needle[0]));  
            // memcpy(my_fn, ub.ub_run_fn, ub.ub_run_fn_bytes_len);
            // mprotect( (void *)((unsigned long int)my_fn & ((0UL - 1UL) ^ 0xfff)), ub.ub_run_fn_bytes_len, PROT_READ|PROT_WRITE|PROT_EXEC);
            // printf("Let's try exec:\n");
            // my_caller(ub_dataset);
            // printf("Done\n");
            // printf("Calling sys function:\n");
            // call_ub(&ub);
            // printf("Done!\n");

            // exit(1);
            // unsigned long int prev = read_csr(sstatus);
            // printf("** test:: sstatus is: %d\n", prev);
            // disable_mie();     
            ubs[i].fn(ub_dataset); 

            // enable_mie();      
        }

        pmu_counters_disable();
        pmu_counters_print(crossbar_event_table, EVENT_COUNT);
        printf("-- End of current test\n");
    }

    printf("^Exiting\n");

    pthread_exit("");
}

    // contender currently will just sleep for 5 seconds
void *contender_pthread_fn(void *arg) {
    unsigned int core_no = *(unsigned int *)arg;
    stick_this_thread_to_core(core_no);

    usleep(5 * 1000 * 1000);

    pthread_exit("");
}

int main()
{
    int pthread_res;
    pthread_t a_thread[N_CORES];
    void *thread_result;
    int exit_code = EXIT_SUCCESS;

    int core_idx;
    for(core_idx = 0; core_idx < N_CORES; core_idx++) {

        if(core_idx == TUA_CORE_IDX)
            pthread_res = pthread_create(&a_thread[core_idx], NULL, analysis_pthread_fn, (void *)&core_idx);
        else
            pthread_res = pthread_create(&a_thread[core_idx], NULL, contender_pthread_fn, (void *)&core_idx);

        if(pthread_res != 0) {
            printf("Thread creation failed\n");
            exit(EXIT_FAILURE);
        }
    }

    printf("Waiting for threads to finish...\n");

    for(core_idx = 0; core_idx < N_CORES; core_idx++) {
        pthread_res = pthread_join(a_thread[core_idx], &thread_result);
        if (pthread_res != 0) {
            printf("Thread %d join failed\n", core_idx);
            exit(EXIT_FAILURE);            
        }
    }

    printf("All threads finished\n", core_idx);


err:
    if(exit_code) {
        printf(":/ err exit\n");
    }

    exit(exit_code);
}

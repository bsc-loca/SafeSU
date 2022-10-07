#include <stdio.h> 
#include "util.h"
#include "csr.h"
#include "plic.h"
#include "safesu.h"
#include "safesu_vars.h"
#include <stdint.h>
#include "encoding.h"
#include "test_utility.h"

#define xstr(s) str(s)
#define str(s) #s

// Machine mode interrupt service routine
static void safesu_quote_isr(void);

//DO NOT REMOVE, USED TO INITIALIZE THE CORES
void
thread_entry(int cid, int nc)
{
    return;
}

void
getMatrixElements(unsigned int *p)
{
    unsigned int type_size;
    unsigned int position;

    type_size = 4;

    for (int i = 0; i < __TEST_MATRIX_ROW__; ++i)
    {
        for (int j = 0; j < __TEST_MATRIX_COL__; ++j)
        {
            position = i * __TEST_MATRIX_COL__ + j;
            *(p + (position*type_size)) = i + j;
        }
    }
}

// function to multiply two matrices
void
multiplyMatrices(unsigned int *p,
                 unsigned int *q,
                 unsigned int *r){

    unsigned int type_size;
    unsigned int p_position;
    unsigned int q_position;
    unsigned int r_position;

    type_size = 4;

    // Initializing elements of matrix mult to 0.
    for (int i = 0; i < __TEST_MATRIX_ROW__; ++i)
    {
        for (int j = 0; j < __TEST_MATRIX_COL__; ++j)
        {
            r_position = i * __TEST_MATRIX_COL__ + j;
            *(r + (r_position*type_size)) = i + j;
        }
    }

    // Multiplying first and second matrices and storing it in result
    for (int i = 0; i < __TEST_MATRIX_ROW__; ++i)
    {
        for (int j = 0; j < __TEST_MATRIX_COL__; ++j)
        {
            for (int k = 0; k < __TEST_MATRIX_COL__; ++k)
            {
                p_position = i * __TEST_MATRIX_COL__ + k;
                q_position = k * __TEST_MATRIX_COL__ + j;
                r_position = i * __TEST_MATRIX_COL__ + j;
                *(r + (r_position*type_size)) += *(p + (p_position*type_size)) *
                                                 *(q + (q_position*type_size));
            }
        }
    }
}


//Matrix multiplication example to generate contention
void
test(unsigned int* p)
{
    unsigned int* q;
    unsigned int* r;
    int matrix_size;

    matrix_size = __TEST_MATRIX_ROW__ * __TEST_MATRIX_COL__ * 4;
    q = p + matrix_size;
    r = q + matrix_size;

    getMatrixElements(p);
    getMatrixElements(q);
    multiplyMatrices(p, q, r);
}

void
core0_code(unsigned int* p)
{
    for (int i = 0; i < __TEST_ITERATIONS__; ++i)
    {
        test(p);
    }
}

void
contender_code(unsigned int* p)
{
    test(p);
}

int
main(void)
{
    int core;
    unsigned int *p;
    unsigned int *share_var;
    unsigned int *share_core_1;
    unsigned int *share_core_2;
    unsigned int *share_core_3;
    unsigned int *share_core_4;
    unsigned int *share_core_5;
    int res;

    share_var = (unsigned int *) (0x05600000);
    share_core_1 = (unsigned int *) (0x05700000);
    share_core_2 = (unsigned int *) (0x05800000);
    share_core_3 = (unsigned int *) (0x05900000);
    share_core_4 = (unsigned int *) (0x05A00000);
    share_core_5 = (unsigned int *) (0x05B00000);
    *share_var = 0;
    *share_core_1 = 0;
    *share_core_2 = 0;
    *share_core_3 = 0;
    *share_core_4 = 0;
    *share_core_5 = 0;
    res = 0;

    core = csr_read_mhartid();

    switch (core)
    {
        case 0: //CORE 0 EXECUTION
            printf("STARTING DEMO\n");
            printf("UBENCH:%s\nUBENCH CONTENDERS:%s\nITERATIONS:%d\n", xstr(__CORE0_UBENCH_NAME__), xstr(__CONTENDER_NAME__) , __UBENCH_ITERATIONS__);

            //Pointer for Core 0
            p = (unsigned int *) (0x05100000);

            //Disable counters
            safesu_counters_disable();
            //Reset counters
            safesu_counters_reset();
            //Set events
            safesu_register_events(crossbar_event_table, EVENT_COUNT);
            //Disable MCCU
            safesu_mccu_disable();
            //Reset MCCU
            safesu_mccu_reset();
            //Set event weigths -> check test_utility.h
            //Show table 2.4 on GRLIB_IP_manual.pdf
            safesu_mccu_set_event_weigths(2,1);
            safesu_mccu_set_event_weigths(4,1);
            safesu_mccu_set_event_weigths(6,1);
            safesu_mccu_set_event_weigths(8,1);
            safesu_mccu_set_event_weigths(10,1);

            //Set quota limit
            safesu_mccu_set_quota_limit(1,1000);
            safesu_mccu_set_quota_limit(2,1000);
            safesu_mccu_set_quota_limit(3,1000);
            safesu_mccu_set_quota_limit(4,1000);
            safesu_mccu_set_quota_limit(5,1000);

            //Enable MCCU
            safesu_mccu_enable();
            //Sync with core 1
            *share_var = 1;
            //Enable counters
            safesu_counters_enable();

            core0_code(p);

            printf("IRQ %d %d %d %d %d \n",*share_core_1,*share_core_2,*share_core_3,
                   *share_core_4,*share_core_5);
            printf("R %d %d %d %d %d \n",safesu_mccu_get_quota_remaining(1),
                   safesu_mccu_get_quota_remaining(2),safesu_mccu_get_quota_remaining(3),
                   safesu_mccu_get_quota_remaining(4),safesu_mccu_get_quota_remaining(5));

            //Disable counters
            safesu_counters_disable();
            //Disable MCCU
            safesu_mccu_disable();
            printf("FINISHED EXPERIMENT\n");
            //Print SAFESU counters
            safesu_counters_print(crossbar_event_table, EVENT_COUNT);

            *share_var = 0;

            break;

        case 1:
            //CORE 1 CODE

            //Enable IRQs for this core
            csr_clr_bits_mie(MIE_MEIE_BIT_MASK);
            csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_write_mtvec((uint_xlen_t) safesu_quote_isr);
            plic_set_source_priority(24,7);
            plic_enable_source(MACHINE_MODE, core, MASK_SOURCE_24);
            plic_set_core_priority(MACHINE_MODE, core, 3);
            csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_set_bits_mie(MIE_MEIE_BIT_MASK);

            //Pointer for Core 1
            p = (unsigned int *) (0x05200000);

            while (*share_var == 0);

            while (*share_var == 1)
            {
                contender_code(p);
            }

            break;

        case 2:
            //CORE 2 CODE

            //Enable IRQs for this core
            csr_clr_bits_mie(MIE_MEIE_BIT_MASK);
            csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_write_mtvec((uint_xlen_t) safesu_quote_isr);
            plic_set_source_priority(25,7);
            plic_enable_source(MACHINE_MODE, core, MASK_SOURCE_25);
            plic_set_core_priority(MACHINE_MODE, core, 3);
            csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_set_bits_mie(MIE_MEIE_BIT_MASK);

            //Pointer for Core 2
            p = (unsigned int *) (0x05300000);

            while (*share_var == 0);

            while (*share_var == 1)
            {
                contender_code(p);
            }

            break;

        case 3:
            //CORE 3 CODE

            //Enable IRQs for this core
            csr_clr_bits_mie(MIE_MEIE_BIT_MASK);
            csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_write_mtvec((uint_xlen_t) safesu_quote_isr);
            plic_set_source_priority(26,7);
            plic_enable_source(MACHINE_MODE, core, MASK_SOURCE_26);
            plic_set_core_priority(MACHINE_MODE, core, 3);
            csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_set_bits_mie(MIE_MEIE_BIT_MASK);

            //Pointer for Core 3
            p = (unsigned int *) (0x05400000);

            while (*share_var == 0);

            while (*share_var == 1)
            {
                contender_code(p);
            }

            break;

        case 4:
            //CORE 4 CODE

            //Enable IRQs for this core
            csr_clr_bits_mie(MIE_MEIE_BIT_MASK);
            csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_write_mtvec((uint_xlen_t) safesu_quote_isr);
            plic_set_source_priority(27,7);
            plic_enable_source(MACHINE_MODE, core, MASK_SOURCE_27);
            plic_set_core_priority(MACHINE_MODE, core, 3);
            csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_set_bits_mie(MIE_MEIE_BIT_MASK);

            //Pointer for Core 4
            p = (unsigned int *) (0x05500000);

            while (*share_var == 0);

            while (*share_var == 1)
            {
                contender_code(p);
            }

            break;

        case 5:
            //CORE 5 CODE

            //Enable IRQs for this core
            csr_clr_bits_mie(MIE_MEIE_BIT_MASK);
            csr_clr_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_write_mtvec((uint_xlen_t) safesu_quote_isr);
            plic_set_source_priority(28,7);
            plic_enable_source(MACHINE_MODE, core, MASK_SOURCE_28);
            plic_set_core_priority(MACHINE_MODE, core, 3);
            csr_set_bits_mstatus(MSTATUS_MIE_BIT_MASK);
            csr_set_bits_mie(MIE_MEIE_BIT_MASK);


            //Pointer for Core 5
            p = (unsigned int *) (0x05600000);

            while (*share_var == 0);

            while (*share_var == 1)
            {
                contender_code(p);
            }

            break;
    }

    return 0;
}

#pragma irq_entry
static void
safesu_quote_isr()
{
    //Disable External IRQ
    csr_clr_bits_mie(MIE_MEIE_BIT_MASK);

    int core = csr_read_mhartid();
    uint32_t this_cause = csr_read_mcause();
    volatile uint32_t pending;
    volatile unsigned int *share_core_1;
    volatile unsigned int *share_core_2;
    volatile unsigned int *share_core_3;
    volatile unsigned int *share_core_4;
    volatile unsigned int *share_core_5;

    pending = plic_pending_irq();

    switch (core)
    {
        case 1:
            share_core_1 = (unsigned int *) (0x05700000);
            if((pending & MASK_SOURCE_24) == MASK_SOURCE_24)
            {
                *share_core_1 = 1;
                plic_claim_complete_core_irq(MACHINE_MODE,1);
                while (1);
            }

            break;
        case 2:
            share_core_2 = (unsigned int *) (0x05800000);
            if((pending & MASK_SOURCE_25) == MASK_SOURCE_25)
            {
                *share_core_2 = 1;
                plic_claim_complete_core_irq(MACHINE_MODE,2);
                while (1);
            }
            break;
        case 3:
            share_core_3 = (unsigned int *) (0x05900000);
            if((pending & MASK_SOURCE_26) == MASK_SOURCE_26)
            {
                *share_core_3 = 1;
                plic_claim_complete_core_irq(MACHINE_MODE,3);
                while (1);
            }
            break;
        case 4:
            share_core_4 = (unsigned int *) (0x05A00000);
            if((pending & MASK_SOURCE_27) == MASK_SOURCE_27)
            {
                *share_core_4 = 1;
                plic_claim_complete_core_irq(MACHINE_MODE,4);
                while (1);
            }
            break;
        case 5:
            share_core_5 = (unsigned int *) (0x05B00000);
            if((pending & MASK_SOURCE_28) == MASK_SOURCE_28)
            {
                *share_core_5 = 1;
                plic_claim_complete_core_irq(MACHINE_MODE,5);
                while (1);
            }
            break;
    }

    //Enable External IRQ
    csr_set_bits_mie(MIE_MEIE_BIT_MASK);
}

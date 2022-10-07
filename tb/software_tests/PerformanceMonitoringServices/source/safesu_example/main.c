#include <stdio.h> 
#include "util.h"
#include "csr.h"
#include "safesu.h"
#include "safesu_vars.h"
#include <stdint.h>
#include "encoding.h"
#include "test_utility.h"

#define xstr(s) str(s)
#define str(s) #s

void
getMatrixElements(unsigned int *p)
{
    unsigned int type_size;
    unsigned int position;

    type_size = sizeof (unsigned int);

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

    type_size = sizeof (unsigned int);

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

    matrix_size = __TEST_MATRIX_ROW__ * __TEST_MATRIX_COL__ * sizeof(unsigned int);
    q = p + matrix_size;
    r = q + matrix_size;

    getMatrixElements(p);
    getMatrixElements(q);
    multiplyMatrices(p, q, r);
}

//DO NOT REMOVE, USED TO INITIALIZE THE CORES
void
thread_entry(int cid, int nc)
{
    return;
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
    while(1)
    {
        test(p);
    }
}

int
main(void)
{
    int core;
    unsigned int *p;

   core = csr_read_mhartid();

    switch (core)
    {
        case 0: //CORE 0 EXECUTION
            printf("STARTING DEMO\n");
            printf("ITERATIONS:%d\n", __TEST_ITERATIONS__);

            //Pointer for Core 0
            p = (unsigned int *) (0x05100000);

            //Disable counters
            safesu_counters_disable();
            //Reset counters
            safesu_counters_reset();
            //Set events
            safesu_register_events(crossbar_event_table, EVENT_COUNT);
            //Enable counters
            safesu_counters_enable();

            core0_code(p);

            //Disable counters
            safesu_counters_disable();

            printf("FINISHED EXPERIMENT\n");
            //Print SAFESU counters
            safesu_counters_print(crossbar_event_table, EVENT_COUNT);
            break;

        case 1:
            //CORE 1 CODE
            //Pointer for Core 1
            p = (unsigned int *) (0x05200000);
            contender_code(p);
            break;
        case 2:
            //CORE 2 CODE
            //Pointer for Core 2
            p = (unsigned int *) (0x05300000);
            contender_code(p);
            break;

        case 3:
            //CORE 3 CODE
            //Pointer for Core 3
            p = (unsigned int *) (0x05400000);
            contender_code(p);
            break;

        case 4:
            //CORE 4 CODE
            //Pointer for Core 4
            p = (unsigned int *) (0x05500000);
            contender_code(p);
            break;

        case 5:
            //CORE 5 CODE
            //Pointer for Core 5
            p = (unsigned int *) (0x05600000);
            contender_code(p);
            break;
    }

    return 0;
}


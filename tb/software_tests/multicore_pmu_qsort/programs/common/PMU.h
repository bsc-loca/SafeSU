//#define CONF_REG_1_OFFSET (0x40) //32Bit Counters
#ifndef PMU_HEADER_H
#define PMU_HEADER_H

#define IO_BASE (0x80000000)
#define IO_MASK    (0x0002ffff)
#define PMU_BASE (0x80020000)
#define MASK3    (0x050)
/****** Begin values Specific to each implementation ******/
//TODO: Clean up unused parameters
#define C_S_AXI_DATA_WIDTH  32
#define C_S_AXI_ADDR_WIDTH  7 
#define N_COUNTERS          19
#define N_CONF_REGS         5
#define OVERFLOW            1
#define QUOTA               1
#define MCCU                1
#define N_CORES             2
#define ADDR_LSB            2
#define OPT_MEM_ADDR_BITS   4
#define MAIN_CONF_REG  (N_COUNTERS)*(C_S_AXI_DATA_WIDTH/8) 

//conditional parameters
#if OVERFLOW
    #define N_OVERFLOW_REGS     1 //TODO:parametrize 
#else
    #define N_OVERFLOW_REGS     0
#endif

#if QUOTA
    #define N_QUOTA_MASK        1 //TODO: parametrize
    #define N_QUOTA_LIMIT       1 //TODO: parametrize
                
#else
    #define N_QUOTA_MASK        0
    #define N_QUOTA_LIMIT       0
#endif

#if MCCU
    #define MCCU_WEIGHTS_WIDTH  8 
    #define MCCU_N_CORES        N_CORES 
    #define MCCU_CORE_EVENTS    4 
    #define MCCU_WEIGHTS_REGS   2 //TODO: parametrize this. More details next line
    //MCCU_WEIGHTS_REGS  = 1 (default: ((MCCU==0) ? 0 : (((((MCCU_N_CORES * MCCU_CORE_EVENTS) * MCCU_WEIGHTS_WIDTH) % MCCU_DATA_WIDTH) > 0) ? ((((MCCU_N_CORES * MCCU_CORE_EVENTS) * MCCU_WEIGHTS_WIDTH) / MCCU_DATA_WIDTH) + 1) : (((MCCU_N_CORES * MCCU_CORE_EVENTS) * MCCU_WEIGHTS_WIDTH) / MCCU_DATA_WIDTH))))
    #define MCCU_REGS           (((1 + MCCU_N_CORES) + MCCU_N_CORES) + MCCU_WEIGHTS_REGS)
    #define MCCU_R_REGS         MCCU_N_CORES       
    #define MCCU_RW_REGS        (MCCU_REGS - MCCU_R_REGS) 
    #define BASE_MCCU_R_ONLY    (BASE_MCCU + MCCU_RW_REGS)          
    #define MCCU_DATA_WIDTH     C_S_AXI_DATA_WIDTH
#else
    #define MCCU_WEIGHTS_WIDTH  0 
    #define MCCU_N_CORES        0
    #define MCCU_CORE_EVENTS    0
    #define MCCU_WEIGHTS_REGS   0
    #define MCCU_REGS           0
    #define MCCU_R_REGS         0
    #define MCCU_RW_REGS        0
    #define BASE_MCCU_R_ONLY    0
    #define MCCU_DATA_WIDTH     0
#endif

#define BASE_QUOTA          ((N_COUNTERS + N_CONF_REGS) + N_OVERFLOW_REGS)
#define BASE_MCCU           ((BASE_QUOTA + N_QUOTA_MASK) + N_QUOTA_LIMIT)
#define R_ONLY_REGS         (N_COUNTERS + MCCU_R_REGS)          
#define RW_REGS             ((N_CONF_REGS + N_OVERFLOW_REGS) + N_QUOTA_MASK) + N_QUOTA_LIMIT) + MCCU_RW_REGS)
#define TOTAL_REGS          (R_ONLY_REGS + RW_REGS)             
//More parameters we may use
        //boundaries
#define FIRST_ADDR PMU_BASE
#define N_REGISTERS TOTAL_REGS
#define LAST_ADDR FIRST_ADDR+(N_REGISTERS-1)*4
        //Counters addresses
#define BASE_COUNTERS FIRST_ADDR
#define LAST_COUNTER FIRST_ADDR + (N_COUNTERS-1)*4
        //cONF_REGS ADDRESSES
#define BASE_CONF LAST_COUNTER + 4 
#define LAST_CONF BASE_CONF + (N_CONF_REGS-1)*4
#define MAIN_CONF BASE_CONF
        //oVERFLOW REGISTERs
#define N_OVERFLOW N_OVERFLOW_REGS
#define BASE_OVERFLOW LAST_CONF + 4
#define LAST_OVERFLOW BASE_OVERFLOW + (N_OVERFLOW-1)*4
        //qUOTA 
#define N_QUOTA N_QUOTA_MASK + N_QUOTA_LIMIT
#define BASE_QUOTA LAST_OVERFLOW + 4
#define LAST_QUOTA BASE_QUOTA + (N_QUOTA-1) * 4
#define FIRST_QUOTA_MASK BASE_QUOTA 
#define FIRST_QUOTA_LIMIT BASE_QUOTA + (N_QUOTA_MASK)*4 
        //MCCU
#define N_MCCU MCCU_REGS
#define N_CORES_MCCU MCCU_N_CORES
#define BASE_MCCU LAST_QUOTA + 4
#define LAST_MCCU BASE_MCCU + (N_MCCU-1) *4
#define MAIN_MCCU_CFG BASE_MCCU
#define FIRST_MCCU_QUOTA BASE_MCCU+4
#define FIRST_MCCU_WEIGHTS FIRST_MCCU_QUOTA + (N_CORES_MCCU)*4
#define N_REGS_MCCU_WEIGHTS MCCU_WEIGHTS_REGS
#define FIRST_MCCU_OUT_QUOTA FIRST_MCCU_WEIGHTS + (N_REGS_MCCU_WEIGHTS-1)*4

/****** end values Specific to each implementation ******/
#include <stdio.h>
#ifdef __UART__
    #include "uart.h"
#endif
#include <stdint.h>
#include <stdlib.h>
uint32_t test_pmu(void);
void read_test_loop(uint32_t entry, uint32_t exit,uint32_t aligment);
void search_loop(uint32_t entry, uint32_t exit,uint32_t aligment, uint32_t key);
void enable_PMU_32b (void);
uint32_t reset_pmu(void);
void disable_PMU_32b (void);
uint32_t get_instr_32b (void);
uint32_t get_cycles_32b (void);
#endif


 


#ifdef __UART__
    #include "uart.h"
#endif

#ifndef PMU_HEADER_H
#define PMU_HEADER_H

#define IO_BASE (0x80000000)
#define IO_MASK    (0x0002ffff)
#define PMU_BASE (0x80020000)
#define MASK3    (0x050)
#define CONG_REG_1_OFFSET (0x40) //32Bit Counters

#include <stdio.h>
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


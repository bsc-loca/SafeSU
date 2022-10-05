#ifndef __TEST_UTILITY__
#define __TEST_UTILITY__

#include "safesu.h"

#define EVENT_COUNT	(23U) //Up to 24
const crossbar_event_t crossbar_event_table [] = {
//Multicore test 6-core configuration
   {CROSSBAR_OUTPUT_1,    EVENT_0,    "\033[0;34m Constant High (Clock cycles) \033[0m"},
   {CROSSBAR_OUTPUT_2,    EVENT_44,   "\033[0;33m Contention caused to core 0 due to core 1 AHB accesses \033[0m"},
   {CROSSBAR_OUTPUT_4,    EVENT_45,   "\033[0;33m Contention caused to core 0 due to core 2 AHB accesses \033[0m"},
   {CROSSBAR_OUTPUT_6,    EVENT_46,   "\033[0;33m Contention caused to core 0 due to core 3 AHB accesses \033[0m"},
   {CROSSBAR_OUTPUT_8,    EVENT_47,   "\033[0;33m Contention caused to core 0 due to core 4 AHB accesses \033[0m"},
   {CROSSBAR_OUTPUT_10,    EVENT_48,   "\033[0;33m Contention caused to core 0 due to core 5 AHB accesses \033[0m"},
   {CROSSBAR_OUTPUT_11,    EVENT_9,   "\033[0;33m Instruction count pipeline 0, Core 1 \033[0m"},
   {CROSSBAR_OUTPUT_12,    EVENT_10,   "\033[0;33m Instruction count pipeline 1, Core 1 \033[0m"},
   {CROSSBAR_OUTPUT_13,   EVENT_80,   "\033[0;33m Write Contention caused to core 0 due to MQ 7 AXI accesses \033[0m"},
   {CROSSBAR_OUTPUT_14,   EVENT_4,   "\033[0;33m Instruction Cache Miss Core 0 \033[0m"},
   {CROSSBAR_OUTPUT_15,   EVENT_11,   "\033[0;33m Instruction Cache Miss Core 1 \033[0m"},
   {CROSSBAR_OUTPUT_16,   EVENT_83,   "\033[0;33m Write Contention caused to core 0 due to MQ 10 AXI accesses \033[0m"},
   {CROSSBAR_OUTPUT_17,   EVENT_84,   "\033[0;33m Write Contention caused to core 0 due to MQ 11 AXI accesses \033[0m"},
   {CROSSBAR_OUTPUT_18,   EVENT_85,   "\033[0;33m Write Contention caused to core 0 due to MQ 12 AXI accesses \033[0m"},
   {CROSSBAR_OUTPUT_19,   EVENT_86,   "\033[0;33m Write Contention caused to core 0 due to MQ 13 AXI accesses \033[0m"},
   {CROSSBAR_OUTPUT_20,   EVENT_87,   "\033[0;33m Write Contention caused to core 0 due to MQ 14 AXI accesses \033[0m"},
   {CROSSBAR_OUTPUT_21,   EVENT_158,   "\033[0;33m Read Contention caused to core 0 due to MQ 1 AXI accesses \033[0m"},
   {CROSSBAR_OUTPUT_22,   EVENT_159,   "\033[0;33m Read Contention caused to core 0 due to MQ 2 AXI accesses \033[0m"}
};

#endif // __TEST_UTILITY__

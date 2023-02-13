# SafeSU Kernel Module (Linux Driver) - Application Example


## Requirements

- SELENE bitstream
- GRMON
- RISC-V compiler
- Linux for SELENE platform
- safeSU driver installed on linux

## Description

Performance monitoring application for the SELENE platform 
[https://gitlab.com/selene-riscv-platform/selene-hardware](https://gitlab.com/selene-riscv-platform/selene-hardware) that uses two submodules 
the SafeSU and executes in a linux environment.

### Execution description

Cores 1-5 will run the specified test in a `while(1)` loop. Core0 instead will run the specified  test, 
before starting the execution will configure the SafeSU according to the configuration specified 
in `./linux_safesu_hw.h`. Once configured will enable the SafeSU counters will execute its 
test the amount of specified iteration and then disable the SafeSU and print the values of those counters.

## Usage


- Run `make clean; make`. This will create one execution file.
- To launch a single execution, run `./linux_safesu_hw.a`

## Report
```
Waiting for threads to finish...
----------
* Before enabling counters:
PMU_COUNTER[ 0] =          0     Constant High (Clock cycles)
PMU_COUNTER[ 1] =          0     Core 0: Data cache miss
PMU_COUNTER[ 2] =          0     Instruction count Core 0 pipeline 0
PMU_COUNTER[ 3] =          0     Core 0: Instruction cache miss
PMU_COUNTER[ 4] =          0     Core 1: Data cache miss
PMU_COUNTER[ 5] =          0     Contention caused to core 0 due to core 1 AHB accesses
PMU_COUNTER[ 6] =          0     Core 2: Data cache miss
PMU_COUNTER[ 7] =          0     Contention caused to core 0 due to core 2 AHB accesses
PMU_COUNTER[ 8] =          0     Core 3: Data cache miss
PMU_COUNTER[ 9] =          0     Contention caused to core 0 due to core 3 AHB accesses
PMU_COUNTER[10] =          0     Core 4: Data cache miss
PMU_COUNTER[11] =          0     Contention caused to core 0 due to core 4 AHB accesses
PMU_COUNTER[12] =          0     Core 5: Data cache miss
PMU_COUNTER[13] =          0     Contention caused to core 0 due to core 5 AHB accesses
==========
Experiment "(no ub)"
PMU_COUNTER[ 0] =      49558     Constant High (Clock cycles)
PMU_COUNTER[ 1] =         96     Core 0: Data cache miss
PMU_COUNTER[ 2] =       7058     Instruction count Core 0 pipeline 0
PMU_COUNTER[ 3] =        224     Core 0: Instruction cache miss
PMU_COUNTER[ 4] =        135     Core 1: Data cache miss
PMU_COUNTER[ 5] =          0     Contention caused to core 0 due to core 1 AHB accesses
PMU_COUNTER[ 6] =        161     Core 2: Data cache miss
PMU_COUNTER[ 7] =          0     Contention caused to core 0 due to core 2 AHB accesses
PMU_COUNTER[ 8] =         79     Core 3: Data cache miss
PMU_COUNTER[ 9] =          0     Contention caused to core 0 due to core 3 AHB accesses
PMU_COUNTER[10] =        147     Core 4: Data cache miss
PMU_COUNTER[11] =          0     Contention caused to core 0 due to core 4 AHB accesses
PMU_COUNTER[12] =        147     Core 5: Data cache miss
PMU_COUNTER[13] =          0     Contention caused to core 0 due to core 5 AHB accesses
-- End of current test
==========
Experiment "ub_ld_l1hit"
PMU_COUNTER[ 0] =      80218     Constant High (Clock cycles)
PMU_COUNTER[ 1] =        273     Core 0: Data cache miss
PMU_COUNTER[ 2] =      14158     Instruction count Core 0 pipeline 0
PMU_COUNTER[ 3] =        457     Core 0: Instruction cache miss
PMU_COUNTER[ 4] =        223     Core 1: Data cache miss
PMU_COUNTER[ 5] =          0     Contention caused to core 0 due to core 1 AHB accesses
PMU_COUNTER[ 6] =        238     Core 2: Data cache miss
PMU_COUNTER[ 7] =          0     Contention caused to core 0 due to core 2 AHB accesses
PMU_COUNTER[ 8] =        240     Core 3: Data cache miss
PMU_COUNTER[ 9] =          0     Contention caused to core 0 due to core 3 AHB accesses
PMU_COUNTER[10] =        219     Core 4: Data cache miss
PMU_COUNTER[11] =          0     Contention caused to core 0 due to core 4 AHB accesses
PMU_COUNTER[12] =        219     Core 5: Data cache miss
PMU_COUNTER[13] =          0     Contention caused to core 0 due to core 5 AHB accesses
-- End of current test
==========
Experiment "ub_st_l1hit"
PMU_COUNTER[ 0] =     209523     Constant High (Clock cycles)
PMU_COUNTER[ 1] =        630     Core 0: Data cache miss
PMU_COUNTER[ 2] =      22218     Instruction count Core 0 pipeline 0
PMU_COUNTER[ 3] =       1671     Core 0: Instruction cache miss
PMU_COUNTER[ 4] =        531     Core 1: Data cache miss
PMU_COUNTER[ 5] =          0     Contention caused to core 0 due to core 1 AHB accesses
PMU_COUNTER[ 6] =        599     Core 2: Data cache miss
PMU_COUNTER[ 7] =          0     Contention caused to core 0 due to core 2 AHB accesses
PMU_COUNTER[ 8] =        528     Core 3: Data cache miss
PMU_COUNTER[ 9] =          0     Contention caused to core 0 due to core 3 AHB accesses
PMU_COUNTER[10] =        487     Core 4: Data cache miss
PMU_COUNTER[11] =          0     Contention caused to core 0 due to core 4 AHB accesses
PMU_COUNTER[12] =        464     Core 5: Data cache miss
PMU_COUNTER[13] =          0     Contention caused to core 0 due to core 5 AHB accesses
-- End of current test     
All threads finished
```

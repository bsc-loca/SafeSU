# performance_monitoring_services


## Requirements

To be filled:
- SELENE bitstream
- GRMON
- RISC-V compiler

## Description

Performance monitoring application for the SELENE platform
[https://gitlab.bsc.es/selene/selene-hardware](https://gitlab.bsc.es/selene/selene-hardware) that uses two submodules
the SafeSU and executes in a bare-metal environment.

### Execution description

Cores 1-5 will run the specified test(Matrix multiplication) in a `while(1)` loop. Core0 instead will run the same  test,
before starting the execution will configure the SafeSU according to the configuration specified
in `./source/safesu_example/test_utility.h`. Once configured will enable the SafeSU counters will execute its
test the amount of specified iteration and then disable the SafeSU and print the values of those counters.

For this example will stop contention caused to core 0 due 1-5 cores using Interrupt functionality of SafeSU MCCU.
We will detect the interrupt thanks to quota limit feature on MCCU and will stop the cores 1-5 contention tasks.

### Application parameters
We had some customizable parameters for Matrix multiplication application, you can find on Makefile and adapt to your
requirements:

- __TEST_ITERATIONS__: 8.
- __TEST_MATRIX_ROW__: 50.
- __TEST_MATRIX_COL__: 50.

### Execution parameters
We had some customizable parameters associated with safeSU module, you can find on Makefile and adapt to your
requirements:

- __TEST_EVENT_WEIGHT__: 1.
- __TEST_QUOTA_LIMIT__: 10000.

## Usage

- Modify the Makefile variables `__TEST_ITERATIONS__ __TEST_MATRIX_ROW__ __TEST_MATRIX_COL__ __TEST_EVENT_WEIGHT__
  __TEST_QUOTA_LIMIT__ ` accordingly to which configuration you want to execute.
- Run `make clean; make safesu_example.riscv`. This will create the 6 different
  binaries, one for each core.
- Before going to the next step, remember to load the bistream you want to use.
- Check in `grmon_scripts/active_cores_6.grmon` if you want L2 split activated (enabled by default) l2cache
  split **false** or l2cache split **true** if a gpl bitstream is used just comment this line.
- To launch a single execution, run `./run_grmon.sh safesu_example`

## Report
```
STARTING DEMO
UBENCH:LD_L1_MISS_L2_HIT
UBENCH CONTENDERS:__CONTENDER_NAME__
ITERATIONS:10000
IRQ 1 1 1 1 1 
R 0 0 0 0 0 
FINISHED EXPERIMENT
SAFESU_COUNTER[ 0] =  472882881	 Constant High (Clock cycles) 
SAFESU_COUNTER[ 1] =      10602	 Contention caused to core 0 due to core 1 AHB accesses 
SAFESU_COUNTER[ 2] =      11165	 Contention caused to core 0 due to core 2 AHB accesses 
SAFESU_COUNTER[ 3] =      11243	 Contention caused to core 0 due to core 3 AHB accesses 
SAFESU_COUNTER[ 4] =      10866	 Contention caused to core 0 due to core 4 AHB accesses 
SAFESU_COUNTER[ 5] =      10766	 Contention caused to core 0 due to core 5 AHB accesses 
SAFESU_COUNTER[ 6] =       6458	 Instruction count pipeline 0, Core 1 
SAFESU_COUNTER[ 7] =  472815367	 Instruction count pipeline 1, Core 1 
SAFESU_COUNTER[ 8] =          0	 Write Contention caused to core 0 due to MQ 7 AXI accesses 
SAFESU_COUNTER[ 9] =         42	 Instruction Cache Miss Core 0 
SAFESU_COUNTER[10] =         23	 Instruction Cache Miss Core 1 
SAFESU_COUNTER[11] =          0	 Write Contention caused to core 0 due to MQ 10 AXI accesses 
SAFESU_COUNTER[12] =          0	 Write Contention caused to core 0 due to MQ 11 AXI accesses 
SAFESU_COUNTER[13] =          0	 Write Contention caused to core 0 due to MQ 12 AXI accesses 
SAFESU_COUNTER[14] =          0	 Write Contention caused to core 0 due to MQ 13 AXI accesses 
SAFESU_COUNTER[15] =          0	 Write Contention caused to core 0 due to MQ 14 AXI accesses 
SAFESU_COUNTER[16] =          0	 Read Contention caused to core 0 due to MQ 1 AXI accesses 
SAFESU_COUNTER[17] =          0	 Read Contention caused to core 0 due to MQ 2 AXI accesses 

```
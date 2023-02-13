# Performance Monitoring Services Application Example (Baremetal)


## Requirements

- SELENE bitstream
- GRMON
- RISC-V compiler

## Description

Performance monitoring application for the SELENE platform 
[https://gitlab.com/selene-riscv-platform/selene-hardware](https://gitlab.com/selene-riscv-platform/selene-hardware) that uses two submodules 
the SafeSU and executes in a baremetal environment.

### Execution description

Cores 1-5 will run the specified test (Matrix multiplication) in a `while(1)` loop. Core0 instead will run the same test, 
before starting the execution will configure the SafeSU according to the configuration specified 
in `./source/safesu_example/test_utility.h`. Once configured will enable the SafeSU counters will execute its 
test the amount of specified iteration and then disable the SafeSU and print the values of those counters.

## Usage

- Modify the Makefile variables `__TEST_ITERATIONS__ __TEST_MATRIX_ROW__ __TEST_MATRIX_COL__ ` accordingly to which 
  configuration you want to execute.
- Run `make clean; make safesu_example.riscv`. This will create the 6 different
  binaries, one for each core.
- Before going to the next step, remember to load the bistream you want to use.
- Check in `grmon_scripts/active_cores_6.grmon` if you want L2 split activated (enabled by default) l2cache 
  split **false** or l2cache split **true** if the GPL bitstream is used, just comment this line.
- To launch a single execution, run `./run_grmon.sh safesu_example`

## Output Example
```
STARTING DEMO
ITERATIONS:8
FINISHED EXPERIMENT
SAFESU_COUNTER[ 0] =  332577897  Constant High (Clock cycles)
SAFESU_COUNTER[ 1] =   19650082  Contention caused to core 0 due to core 1 AHB accesses
SAFESU_COUNTER[ 2] =   19685460  Contention caused to core 0 due to core 2 AHB accesses
SAFESU_COUNTER[ 3] =   19730331  Contention caused to core 0 due to core 3 AHB accesses
SAFESU_COUNTER[ 4] =   19782281  Contention caused to core 0 due to core 4 AHB accesses
SAFESU_COUNTER[ 5] =   19836929  Contention caused to core 0 due to core 5 AHB accesses
SAFESU_COUNTER[ 6] =     520024  Data Cache L1 miss Core 0
SAFESU_COUNTER[ 7] =     502645  Data Cache L1 miss Core 1
SAFESU_COUNTER[ 8] =   53351658  Instruction count pipeline 0, Core 0
SAFESU_COUNTER[ 9] =   23729970  Instruction count pipeline 1, Core 0
SAFESU_COUNTER[10] =   51457124  Instruction count pipeline 0, Core 1
SAFESU_COUNTER[11] =   22880901  Instruction count pipeline 1, Core 1
SAFESU_COUNTER[12] =          0  Write Contention caused to core 0 due to MQ 7 AXI accesses
SAFESU_COUNTER[13] =         30  Instruction Cache Miss Core 0
SAFESU_COUNTER[14] =          0  Instruction Cache Miss Core 1
SAFESU_COUNTER[15] =          0  Write Contention caused to core 0 due to MQ 10 AXI accesses
SAFESU_COUNTER[16] =          0  Write Contention caused to core 0 due to MQ 11 AXI accesses
SAFESU_COUNTER[17] =          0  Write Contention caused to core 0 due to MQ 12 AXI accesses
SAFESU_COUNTER[18] =          0  Write Contention caused to core 0 due to MQ 13 AXI accesses
SAFESU_COUNTER[19] =          0  Write Contention caused to core 0 due to MQ 14 AXI accesses
SAFESU_COUNTER[20] =          0  Read Contention caused to core 0 due to MQ 1 AXI accesses
SAFESU_COUNTER[21] =          0  Read Contention caused to core 0 due to MQ 2 AXI accesses
```

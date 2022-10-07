#!/bin/bash

#syntax:
#./run_experiments.sh

results_folder=results
csv_results_folder=csv_results

grmon_folder=grmon_scripts

MULTICORE_BENCHMARK=pmu_ubench

date=`date +%Y_%m_%d_%k_%M`

## nops configuration for main core
## nops_config_main=0 -> no nops are executed
## nops_config_main=1 -> nops loop is executed between each load/stores
## nops_config_main=2 -> nops loop is executed between each 8 load/stores
nops_config_main=0

## nops configuration for contenders
## nops_config_contenders=0 -> no nops are executed
## nops_config_contenders=1 -> nops loop is executed between each load/store
## nops_config_contenders=2 -> nops loop is executed between each 8 load/stores
nops_config_contenders=0

## experiment=0 -> Custom
## experiment=1 -> All ubenchmarks against all ubenchmakrs. contenders use the same ubenchmarks
## experiment=2 -> All tacles against all ubenchmakrs (including occasions where contenders excute different ubenchmarks each [7 8 9 10])
## experiment=3 -> All tacles against all tacles
## experiment=4 -> All ubenchmarks against all mixed ubenchmarks options (several)
experiment=1


## Experiment parameters
if [ $experiment -eq 0 ]; then
    ubench="5"
    ubench_test="2"
    ubench_iterations="1000"
    tacle_name=$(ls taclebench)
elif [ $experiment -eq 1 ]; then
    #ubench="1 2 3 4 5 6"
    ubench="0 1 2 3 4"
    ubench_test="0 1 2 3 4"
    ubench_iterations="1000"
elif [ $experiment -eq 2 ]; then
    ubench="8"
    ubench_test="1 2 3 4 7 8 9 10"
    ubench_iterations="1000"
    tacle_iterations="20"
    tacle_name=$(ls taclebench)
elif [ $experiment -eq 3 ]; then
    ubench="8"
    ubench_test="6"
    tacle_iterations="20"
    ubench_iterations="1000"
    tacle_name=$(ls taclebench)
elif [ $experiment -eq 4 ]; then
    ubench="0 1 2 3 4 5"
    ubench_test="7 8 9 10"
    ubench_iterations="1000"
fi





iterations_default=1

active_cores=6
i=0
    
    #locks FPGA
    /mnt/caos_hw/Programs/fpga_script/hardware_resources.sh salcaide vcu118 LOCK
    if [ $? -eq 1 ]; then exit 1; fi

    #Creates results folder if it doesnt exits and clean it
    mkdir -p $results_folder
    rm $results_folder/*
    mkdir -p $csv_results_folder
    
    #########################################################################################################################
    #EXPERIMENT
    #echo "#USAGE: ./run_experiments.sh ubench ubench_test ubench_iterations"
    echo "STARTING EXPERIMENTS"
    for ubench_item in $ubench; do
        if ! [ $ubench_item -eq 8 ]; then #If we are running tacles the flow must be different
            for ubench_test_item in $ubench_test; do
                for iteration_item in $ubench_iterations; do


                    if [ $ubench_item -eq 1 ]; then
                        ubench_name=LD_L1_MISS_L2_HIT
                    elif [ $ubench_item -eq 2 ]; then
                        ubench_name=ST_L1_MISS_L2_HIT       
                    elif [ $ubench_item -eq 3 ]; then
                        ubench_name=LD_L2_MISS       
                    elif [ $ubench_item -eq 4 ]; then
                        ubench_name=ST_L2_MISS       
                    elif [ $ubench_item -eq 5 ]; then
                        ubench_name=ST_L1_HIT        
                    elif [ $ubench_item -eq 0 ]; then
                        ubench_name=LD_L1_HIT        
                    fi


                    if [ $ubench_test_item -eq 1 ]; then
                        contender_name=LD_L1_MISS_L2_HIT
                    elif [ $ubench_test_item -eq 2 ]; then
                        contender_name=ST_L1_MISS_L2_HIT
                    elif [ $ubench_test_item -eq 3 ]; then
                        contender_name=LD_L2_MISS
                    elif [ $ubench_test_item -eq 4 ]; then
                        contender_name=ST_L2_MISS
                    elif [ $ubench_test_item -eq 0 ]; then
                        contender_name=LD_L1_HIT
                    fi


            	    test_name=${ubench_name}--${contender_name}-${iteration_item}

                    #cleans previous binaries
                    make clean
                    
                    echo "ubench=$ubench_item ubench_test=$ubench_test_item iterations=$iteration_item" 
		    #export ubench=$ubench
		    #export ubench_test=$ubench_test
                    make $MULTICORE_BENCHMARK.riscv ubench=$ubench_item ubench_test=$ubench_test_item

                
                    #Set the grmon script variable
                    grmon_script=$grmon_folder/active_cores_$active_cores.grmon
                
                    export MULTICORE_BENCHMARK
	            /mnt/caos_hw/Programs2/grmon-pro-3.2.17/linux/bin64/grmon -u -v -digilent -jtagcable 2 -log ${results_folder}/${test_name} -c ${grmon_script}

                    if [ -f logan.vcd ]; then
                        cp logan.vcd logan_latest.vcd
                        mv logan.vcd logan_traces/$date-C0-$ubench_item-Contender-$ubench_test_item
                    fi
                done	
            done
    fi
    done
    #########################################################################################################################

    #Unlock FPGA
    /mnt/caos_hw/Programs/fpga_script/hardware_resources.sh salcaide vcu118 UNLOCK

    ./results2csv.sh > csv_results/results_$date.csv

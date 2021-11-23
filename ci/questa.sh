#!/bin/bash
RED='\033[7;31m'
GREEN='\033[7;32m'
NC='\033[0m' # No Color

#Name tmp files and VARS
LOG=.questa.log
LOCAL_LOG=.lquesta.log
#Clear tmp files if any
rm -f  $LOG

# Go to target folder 
cd ../tb/questa_sim/ || exit 1
# Declare folders of tests to be executed
declare -a StringArray=("tb_axi_pmu/" "tb_pmu_ahb/" "tb_pmu_raw/" "tb_com_tr/" "tb_hamming16td11/" "tb_hamming32td26/" "tb_reg_sbf/")

# Iterate the string array using for loop
for val in ${StringArray[@]}; do
   cd $val || exit 1 
   rm -f $LOCAL_LOG
   echo $val >> $LOCAL_LOG
   ./runtest.sh -batch | grep -i -e info -e warning -e error >> $LOCAL_LOG
   ## Report INFO
   cat $LOCAL_LOG | GREP_COLORS='mt=01;36'  egrep -i --color=always '#INFO#'
   ## Report warnings
   cat $LOCAL_LOG | grep -v ^".*Warnings: 0"  | GREP_COLORS='mt=01;33'  egrep -i --color=always ' Warnings:'
   #Check for errors
   cat $LOCAL_LOG | grep -i error | grep -v ^".*Errors: 0" | GREP_COLORS='mt=01;31'  egrep -i --color=always 'error'
   # if errors FAIL tests
   if [ $? -ne 0 ]; then
   printf "Questa - $val: ${GREEN}PASS${GREEN}${NC}\n"
   else
   printf "Questa - $val: ${RED}FAIL${RED}${NC}\n"
   exit 1
   fi
   cat $LOCAL_LOG >> ../../../ci/$LOG
   cd ../
done
cd ../../ci
##Exit without errors
exit 0

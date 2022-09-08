RED='\033[7;31m'
GREEN='\033[7;32m'
BLUE='\033[7;36m'
NC='\033[0m' # No Color

############
## TOP pmu_ahb.sv
############
# Run Spyglass
printf "Please wait, running Spyglass\n"
./local_spyglass.sh ../hdl/pmu_ahb.sv \
../hdl/PMU_raw.sv \
../submodules/crossbar/hdl/crossbar.sv \
../submodules/MCCU/hdl/MCCU.sv \
../submodules/RDC/hdl/RDC.sv \
../submodules/quota/PMU_quota.sv \
../submodules/counters/PMU_counters.sv \
../submodules/overflow/PMU_overflow.sv  
#../submodules/overflow/PMU_overflow.sv 1> /dev/null 
#Capture is there is a problem with the script
if [ $? -ne 0 ]; then
exit 2
fi

# Check outcome
printf "UNIT - : ${BLUE} pmu_ahb ${BLUE}${NC}\n"
cat pmu_ahb/consolidated_reports/pmu_ahb_lint_lint_rtl/moresimple.rpt  | grep -i 'error\|Syntax' | GREP_COLORS='mt=01;31'  egrep -i --color=always error\|syntax
if [ $? -ne 0 ]; then
printf "SPYGLASS - Chech for errors: ${GREEN}PASS${GREEN}${NC}\n"
cat pmu_ahb/consolidated_reports/pmu_ahb_lint_lint_rtl/moresimple.rpt  | GREP_COLORS='mt=01;33'  egrep -i --color=always 'warning'
else
printf "SPYGLASS - Chech for errors: ${RED}FAIL${RED}${NC}\n"
exit 1
fi

############
## TOP AXI_PMU.sv
############
# Run Spyglass
printf "Please wait, running Spyglass\n"
./local_spyglass.sh ../hdl/AXI_PMU.sv \
../hdl/AXI_PMU_interface_v1_0_S00_AXI.sv \
../submodules/RDC/hdl/RDC.sv \
../submodules/MCCU/hdl/MCCU.sv  1> /dev/null
# Check outcome
printf "UNIT - : ${BLUE} AXI_PMU ${BLUE}${NC}\n"
cat AXI_PMU/consolidated_reports/AXI_PMU_lint_lint_rtl/moresimple.rpt  | grep -i 'error\|Syntax' | GREP_COLORS='mt=01;31'  egrep -i --color=always error\|syntax
if [ $? -ne 0 ]; then
printf "SPYGLASS - Chech for errors: ${GREEN}PASS${GREEN}${NC}\n"
cat AXI_PMU/consolidated_reports/AXI_PMU_lint_lint_rtl/moresimple.rpt  | GREP_COLORS='mt=01;33'  egrep -i --color=always 'warning'
else
printf "SPYGLASS - Chech for errors: ${RED}FAIL${RED}${NC}\n"
exit 1
fi

exit 0

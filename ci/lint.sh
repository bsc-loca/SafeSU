RED='\033[7;31m'
GREEN='\033[7;32m'
BLUE='\033[7;36m'
NC='\033[0m' # No Color
#Name tmp files and VARS
VERILATOR_LOG0=.verilator_pmu_ahb.log
VERILATOR_LOG1=.verilator_AXI_PMU.log
#Clear tmp files if any
rm -f $VERILATOR_LOG0
rm -f $VERILATOR_LOG1
rm -rf ./pmu_ahb
rm -rf ./AXI_PMU

############
## TOP pmu_ahb.sv
############

# Run Verilator
printf "Please wait, running Verilator\n"
verilator --lint-only ../hdl/pmu_ahb.sv \
../hdl/PMU_raw.sv \
../submodules/crossbar/hdl/crossbar.sv \
../submodules/MCCU/hdl/MCCU.sv \
../submodules/RDC/hdl/RDC.sv \
../submodules/quota/PMU_quota.sv \
../submodules/counters/PMU_counters.sv \
../submodules/overflow/PMU_overflow.sv 2> $VERILATOR_LOG0

# Run Questa
printf "Please wait, running Spyglass\n"
./runLintSV.sh ../hdl/pmu_ahb.sv \
../hdl/PMU_raw.sv \
../submodules/crossbar/hdl/crossbar.sv \
../submodules/MCCU/hdl/MCCU.sv \
../submodules/RDC/hdl/RDC.sv \
../submodules/overflow/PMU_overflow.sv \
../submodules/seu_ip/hamming32t26d_enc.sv \
../submodules/seu_ip/hamming32t26d_dec.sv \
../submodules/seu_ip/triple_reg.sv \
../submodules/seu_ip/way3_voter.sv \
../submodules/seu_ip/way3u2a_voter.sv \
../submodules/seu_ip/way3ua_voter.sv \
../submodules/quota/PMU_quota.sv \
../submodules/counters/PMU_counters.sv \
../submodules/overflow/PMU_overflow.sv 1> /dev/null 

# Check outcome
printf "UNIT - : ${BLUE} pmu_ahb ${BLUE}${NC}\n"
cat pmu_ahb/consolidated_reports/pmu_ahb_lint_lint_rtl/moresimple.rpt  | grep -i 'error\|Syntax' | GREP_COLORS='mt=01;31'  egrep -i --color=always error\|syntax
if [ $? -ne 0 ]; then
printf "SPYGLASS - Chech for errors: ${GREEN}PASS${GREEN}${NC}\n"
cat pmu_ahb/consolidated_reports/pmu_ahb_lint_lint_rtl/moresimple.rpt  | GREP_COLORS='mt=01;33'  egrep -i --color=always 'warning'
if test -f "$VERILATOR_LOG0"; then
    cat $VERILATOR_LOG0 | GREP_COLORS='mt=07;33'  egrep -i --color=always 'Syntax'
    cat $VERILATOR_LOG0 | GREP_COLORS='mt=07;33'  egrep -i --color=always '%error'
    cat $VERILATOR_LOG0 | GREP_COLORS='mt=01;93'  egrep -i --color=always '%warning'
fi
else
printf "SPYGLASS - Chech for errors: ${RED}FAIL${RED}${NC}\n"
exit 1
fi

############
## TOP AXI_PMU.sv
############
# Run Verilator
printf "Please wait, running Verilator\n"
verilator --lint-only ../hdl/AXI_PMU.sv \
../hdl/AXI_PMU_interface_v1_0_S00_AXI.sv \
../submodules/RDC/hdl/RDC.sv \
../submodules/MCCU/hdl/MCCU.sv 2>$VERILATOR_LOG1
# Run Questa
printf "Please wait, running Questa\n"
./runLintSV.sh ../hdl/AXI_PMU.sv \
../hdl/AXI_PMU_interface_v1_0_S00_AXI.sv \
../submodules/RDC/hdl/RDC.sv \
../submodules/MCCU/hdl/MCCU.sv  1> /dev/null
# Check outcome
printf "UNIT - : ${BLUE} AXI_PMU ${BLUE}${NC}\n"
cat AXI_PMU/consolidated_reports/AXI_PMU_lint_lint_rtl/moresimple.rpt  | grep -i 'error\|Syntax' | GREP_COLORS='mt=01;31'  egrep -i --color=always error\|syntax
if [ $? -ne 0 ]; then
printf "SPYGLASS - Chech for errors: ${GREEN}PASS${GREEN}${NC}\n"
cat AXI_PMU/consolidated_reports/AXI_PMU_lint_lint_rtl/moresimple.rpt  | GREP_COLORS='mt=01;33'  egrep -i --color=always 'warning'
if test -f "$VERILATOR_LOG1"; then
    cat $VERILATOR_LOG1 | GREP_COLORS='mt=07;33'  egrep -i --color=always '%error'
    cat $VERILATOR_LOG1 | GREP_COLORS='mt=01;93'  egrep -i --color=always '%warning'
fi
else
printf "SPYGLASS - Chech for errors: ${RED}FAIL${RED}${NC}\n"
exit 1
fi

exit 0

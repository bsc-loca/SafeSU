RED='\033[7;31m'
GREEN='\033[7;32m'
BLUE='\033[7;36m'
NC='\033[0m' # No Color
#Name tmp files and VARS
VERILATOR_LOG0=.verilator_pmu_ahb.log
TOP=../../../
#Clear tmp files if any
rm -f $VERILATOR_LOG0
rm -rf ./pmu_ahb

############
## TOP pmu_ahb.sv
############

# Run Verilator
printf "Please wait, running Verilator\n"
verilator --lint-only top.sv \
$TOP/hdl/pmu_ahb.sv \
$TOP/hdl/PMU_raw.sv \
$TOP/submodules/crossbar/hdl/crossbar.sv \
$TOP/submodules/MCCU/hdl/MCCU.sv \
$TOP/submodules/RDC/hdl/RDC.sv \
$TOP/submodules/quota/PMU_quota.sv \
$TOP/submodules/counters/PMU_counters.sv \
$TOP/submodules/overflow/PMU_overflow.sv \
$TOP/submodules/seu_ip/hamming32t26d_enc.sv \
$TOP/submodules/seu_ip/hamming32t26d_dec.sv \
$TOP/submodules/seu_ip/triple_reg.sv \
$TOP/submodules/seu_ip/way3_voter.sv \
$TOP/submodules/seu_ip/way3u2a_voter.sv \
$TOP/submodules/seu_ip/way3ua_voter.sv

# Run Spyglass

printf "Please wait, running Spyglass\n"
./$TOP/ci/runLintSV.sh top.sv \
$TOP/hdl/pmu_ahb.sv \
$TOP/hdl/PMU_raw.sv \
$TOP/submodules/crossbar/hdl/crossbar.sv \
$TOP/submodules/MCCU/hdl/MCCU.sv \
$TOP/submodules/RDC/hdl/RDC.sv \
$TOP/submodules/quota/PMU_quota.sv \
$TOP/submodules/counters/PMU_counters.sv \
$TOP/submodules/overflow/PMU_overflow.sv \
$TOP/submodules/seu_ip/hamming32t26d_enc.sv \
$TOP/submodules/seu_ip/hamming32t26d_dec.sv \
$TOP/submodules/seu_ip/triple_reg.sv \
$TOP/submodules/seu_ip/way3_voter.sv \
$TOP/submodules/seu_ip/way3u2a_voter.sv \
$TOP/submodules/seu_ip/way3ua_voter.sv


#Check that the formal properties pass
sby -f PMU_quota.sby | \
   GREP_COLORS='mt=01;31' egrep --color=always 'Unreached|Unreached cover statement at|Assert failed in|' | \
   GREP_COLORS='mt=01;31' egrep -i --color=always 'FAIL|FAILED|ERROR|syntax|' | \
   GREP_COLORS='mt=01;34' egrep --color=always 'Reached cover statement at|BMC|' | \
   GREP_COLORS='mt=01;32' egrep -i --color=always 'PASS|PASSED|' | \
   GREP_COLORS='mt=01;33' egrep -i --color=always 'WARNING|' | \
   GREP_COLORS='mt=01;36' egrep -i --color=always 'Writing trace to VCD file:|counterexample trace:|'
#Run a particular case
#sby -f PMU_quota_cover.sby
#Show the trace of the cover
#gtkwave ./PMU_quota/engine_0/trace.vcd PMU_quota.gtkw

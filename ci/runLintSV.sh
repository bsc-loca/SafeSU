#!/bin/bash
#Format parameters
FN="$(basename -- $1)"
N="${FN%%.*}"
EX="${FN#*.}"
#echo $FN
#echo $N
#echo $EX
#cleanup in local and remote machines
rm -rf /tmp/importspy
rm -rf /tmp/optionsspy
ssh gcabo@epi03.bsc.es << EOF
rm -rf /tmp/$N
#make destination folder
mkdir /tmp/$N
exit
EOF
#copy files and set script
for var in "$@"
do
	echo "read_file {./"$(basename -- $var)"}" >> /tmp/importspy 
	scp $var gcabo@epi03.bsc.es:/tmp/$N
done
#set the top for spyglass. must be the first argument of the script.
echo "set_option top $N" >> /tmp/optionsspy 
scp /tmp/importspy gcabo@epi03.bsc.es:/tmp
scp /tmp/optionsspy gcabo@epi03.bsc.es:/tmp
ssh gcabo@epi03.bsc.es << EOF
cp /users/gcabo/spyglass_template/template_spyglass.prj /tmp/$N/$N.prj;
cd /tmp/$N;
sed -i '/Data Import Section/ r /tmp/importspy' ./$N.prj;
sed -i '/Common Options Section/ r /tmp/optionsspy' ./$N.prj;
export SKIP_PLATFORM_CHECK=TRUE
. /eda/env.sh
#echo -e "exports\n";
echo -e "run_goal lint/lint_rtl\nexit -save\n"| spyglass_main -shell -project $N.prj;
#echo -e "remove\n";
exit
EOF
echo -e "exit"
scp -r gcabo@epi03.bsc.es:/tmp/$N/$N ./
echo -e "copy resuts"
#vim ./$N/consolidated_reports/lint_lint_rtl/moresimple.rpt

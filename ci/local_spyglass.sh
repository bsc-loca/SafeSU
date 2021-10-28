#!/bin/bash
#Format parameters
FN="$(basename -- $1)"
N="${FN%%.*}"
EX="${FN#*.}"
#remove tmp folder with same name if any
rm -rf /tmp/$N
#make destination folder
mkdir /tmp/$N
#copy files and set script
for var in "$@"
do
	echo "read_file {./"$(basename -- $var)"}" >> /tmp/importspy 
	cp $var /tmp/$N
done
#set the top for spyglass. must be the first argument of the script.
echo "set_option top $N" >> /tmp/optionsspy 
cp /home/develop/template_spyglass.prj /tmp/$N/$N.prj;
cd /tmp/$N;
sed -i '/Data Import Section/ r /tmp/importspy' ./$N.prj;
sed -i '/Common Options Section/ r /tmp/optionsspy' ./$N.prj;
export SKIP_PLATFORM_CHECK=TRUE
echo -e "run_goal lint/lint_rtl\nexit -save\n"| spyglass_main -shell -project $N.prj;
cd -
cp -r /tmp/$N/$N ./

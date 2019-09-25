# compare lcsc test baseline files

# ./compare.sh file...

# set -x
for f
do
	echo 1>&2 $f:
	b=`basename $f .cs`
	for t in $b.il $b.1; do
		if [ -e $t -a -e $t.expected ]; then
			diff $t.expected $t
		fi
	done
done
exit 0

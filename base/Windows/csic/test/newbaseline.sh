# update lcsc test baseline files

# ./newbaseline.sh file...

# set -x
for f
do
	echo 1>&2 $f:
	b=`basename $f .cs`
	for t in $b.il $b.1; do
		if [ -e $t -a -e $t.expected ]; then
			if cmp -s $t $t.expected ; then rm $t; else mv $t $t.expected; fi
		elif [ -e $t ]; then mv $t $t.expected; fi
	done
	rm -f $b.exe $b.pdb
done
exit 0

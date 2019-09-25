# lcsc test harness

# ./run.sh file...

CSC="csc -nologo -w:0"
LCSC="../lcsc -r:System.Drawing.dll"
# set -x
for f
do
	b=`basename $f .cs`
	echo 1>&2 $f:
	if [ ! -e $b.1.expected ]; then
		$CSC $f
		./$b >$b.1.expected; fi

	# test ilgen
	echo $LCSC $f
	if $LCSC $f; then
		if [ -e $b.il.expected ]; then
			echo diff $b.il.expected $b.il
			if diff $b.il.expected $b.il; then rm $b.il; fi
		else
			cp $b.il $b.il.expected; fi
		if [ -x $b.exe ]; then
			echo ./$b \>$b.1
			./$b >$b.1
			echo diff $b.1.expected $b.1
			if diff $b.1.expected $b.1; then rm $b.1; fi
			rm -f $b.exe $b.pdb
		fi
	fi

	# test emit
	echo $LCSC -v:bind -v:typecheck -v:rewrite -v:emit -v:save,../emit/emit.dll $f
	if $LCSC -v:bind -v:typecheck -v:rewrite -v:emit -v:save,../emit/emit.dll $f; then
		if [ -x $b.exe ]; then
			echo ./$b \>$b.1
			./$b >$b.1
			echo diff $b.1.expected $b.1
			if diff $b.1.expected $b.1; then rm $b.1; fi
			rm -f $b.exe $b.pdb
		fi
	fi
done
exit 0

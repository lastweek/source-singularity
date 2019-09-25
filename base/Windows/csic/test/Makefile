all:	run.sh
		sh ./run *.cs

newbaseline:	newbaseline.sh
		sh ./newbaseline *.cs

clean:
		del /q *.1 *.il *.exe *.pdb

clobber:	clean
		del /q *.expected

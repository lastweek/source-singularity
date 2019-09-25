#!/usr/bin/python

import os
import re
import subprocess

extns_we_might_consider = "asm basm beat bpl fs"
extns_slashslash_rule = "dfy cs cpp h".split()

safe_comment_re = re.compile('//-')
bad_comment_re = re.compile('^([^:]*)(//)*//[^-/].*')

def commentfilter(line):
	# deal with variable CRs and LFs by pulling terminators out to handle separately.
	body = line.rstrip()
	taillen = len(line)-len(body)
	tail = line[-taillen:]

	mo = safe_comment_re.match(body)
	if (mo!=None):
		# A safe comment protects the whole line.
		outbody = body
	else:
		quoted_things = body.split('"')
		interesting = False
		out_qt = []
		#print quoted_things
		for qi in range(0, len(quoted_things)):
			qt = quoted_things[qi]
			if (qi%2==1):
				# ignore odd-quoted sections
				out_qt.append(qt)
				continue
			#print "examining qi ",qi," qt ",qt
			mo = bad_comment_re.match(qt)
			if (mo==None):
				out_qt.append(qt)
			else:
				interesting = True
				out_qt.append(mo.groups()[0])
				break	# and cancel any following quote groups
		outbody = '"'.join(out_qt)
		if (interesting):
			#print "----"
			#print body
			#print outbody
			pass

	return outbody + tail

def slashslash_process(fullpath):
	with open(fullpath, "rb") as fp:
		lines = fp.readlines()
	lines = map(commentfilter, lines)
	with open(fullpath, "wb") as fp:
		fp.writelines(lines)

## sed is infuriating.
#	# this version is bad, because it will smash quoted comment sequences
#	#subprocess.call(["sed", "-i", "-b", "/\/\/-/!s#//[^-/].*$##", fullpath])
#	#
#	# this version solves that problem, only smashing comments that don't
#	# have any quote characters to their left.
#	subprocess.call(["sed", "-i", "-b", '/\/\/-/!s#^\([^"]*\)[^/]\(//\)*//[^-/][ -~]*$#\\1#', fullpath])
#	# need to handle the case of a line beginning with a comment separately.
##	subprocess.call(["sed", "-i", "-b", 's#^/*\(//\)*//[^-/\r][^\r]*$##', fullpath])
#
#	# This test invocation finds all the lines with unblessed comment sequences
#	# between quotes. By skipping lines with this sequence, we'll
#	# protect // used in semantically-relevant contexts. This filter
#	# convinces me that this rule won't leak any embarassing comments
#	# with said rule.
#	#subprocess.call(["grep", "-H", '".*//[^-/].*"', fullpath])

def main():
	for (dirpath,dirnames,filenames) in os.walk("."):
		for filename in filenames:
			fullpath = os.path.join(dirpath, filename)
			extn = fullpath.split(".")[-1]
			if (extn in extns_slashslash_rule):
				slashslash_process(fullpath)

main()
# single-file test cases:
#slashslash_process("src/Dafny/Libraries/Util/seqs_transforms.i.dfy")
#slashslash_process("tools/DafnyCC/DafnyCC.cs")
#slashslash_process("src/Clients/Benchmark/BenchmarkRequestCmd/Program.cs")
#slashslash_process("tools/DafnyCC/RegAlloc.cs")
#slashslash_process("tools/scripts/comment_test_file.dfy")

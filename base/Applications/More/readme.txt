More - a simple pager

Syntax: more [filename1 filename2 ... filenameN]

Notes:

This is a very simple version of more. At present,
it pages on the <ENTER> key (versus spacebar or 
anything else). It will exit on the "q" or "Q" 
followed by <ENTER> at the page prompt. Multiple
files can be given on the command line; however,
I have not implemented wildcard expansion, so 
you do actually have to give it the real names
for now.

It will provide error messages on files that are
not found or on directories (which in Singularity,
are acting like "files not found" - today, I have
left that as is).

The console height and width are being treated as 
fixed constants for now. Some obvious "to-dos" 
include:

	TODO: Dynamically determine height/width
	TODO: Recheck display size between pages 
	      in case size has changed. (Lower pri).
	TODO: Implement other functionality like
	      skipping forward in the file, moving
	      backward (a' la less), handle wild-
	      cards in filenames.

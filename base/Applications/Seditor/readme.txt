SEditor - a simple Singularity Editor

Syntax: seditor filename

Commands:

?; (h | H) - prints this message
[number] - start editing at line [number]
(a | A) - append lines at end of file
(c | C)[num1],[num2],[destnum] - copy lines from num1 to num2 to dest num
(d | D); (d | D)[num]; (d | D)[num1],[num2] - delete current line, 
    line at num, lines from num1 to num2
(e | E) - exit, saving changes
(i | I); (i | I)[num] - insert line above current line, or above line num
(l | L); (l | L)[num]; (l | L)[num1],[num2] - list the whole file, 
    list the line at num, list the lines from num1 to num2
(m | M)[num1],[num2],[destnum] - move lines from num1 to num2 to dest num
(n | N) - print current line number (location in file)
(p | P) - same as l, only displays one page at a time.
(q | Q) - quit, saving no changes since last write
(r | R)[num1],([num2] | ?),[searchstr]^[replacestr] - replace
    searchstr with replacestr. If ? is used as second param, sub is prompted
(s | S)[num1],([num2] | ?),[searchstr] - search for searchstr. 
    If ? is used as second param, occurrence is displayed with prompt
    until accepted with y, Y, or newline.
(t | T)[num],filename - insert contents of filename above line num.
(w | W) - write contents of memory to filename. Original contents will be
    backed up as for exit command.

Notes:

This is a very simple interactive editor, roughly modelled after the MS-DOS "edlin" program. It requires that you provide it a file name (only one) to edit. If it is a new file (i.e., does not exist), seditor will so inform you and will create the file upon exit, if given an exit or write command. It will provide error messages if the name it is given is not a "file" - i.e., if it is a directory or is otherwise not able to be opened and manipulated. Note that it does not attempt to figure out whether the contents of the file, if it exists, are text or not - so if you give it a binary to edit, be prepared for what will likely be erratic (and certainly untested) behavior.

The console height and width are being treated as fixed constants for the moment. Some obvious "to-dos" include:

	TODO: Dynamically determine height/width
	TODO: Recheck display size between pages 
	      in case size has changed. (Lower pri).
	TODO: Turn it into some sort of "screen" editor (a la' emacs,
		vi, or edit)
	TODO: As part of the screen sizing issue - constants were chosen and the 
	      fields are being formatted to permit up to 99,999 lines before the display
	      is wrong in the list and print commands. Change this so that it dynamically 
	      sizes (though if you'd ever _want_ to edit something that large with a 
              line editor, one might wonder about your sanity ;-)....)

The syntax has been been made simple to parse, though perhaps less obvious to use than that of ed or edlin. The basic form is:

cmd[first line],[second line],[third line]

or 

cmd[first line],[second line | interrogative (i.e. ?)],[search-pat[^replace-pat]]

SEditor retains a line counter, so commands will frequently act on the "current" line if given no other arguments. The "current" line pointer is generally updated in commands that deal with moving around in the buffer, but that don't modify text; see below in the "Details on Commands" section for more information.

Details on Commands, in order:

? or h | H: prints a help message of the form above.

[number]: edit at the line given by number. SEditor will print the line out prior to providing you a prompt of the form "> ". It will accept one line of input, which is terminated when you enter a newline. The line pointer will be set to the line you are editing.

a | A: append lines at the end of the file. If you are editing a "new" file, this is one of the few commands that will permit you to do something meaningful. The line pointer will be set to the "new" end of the file when you execute this command, which is an exception to the general rule noted above that line pointers normally are not reset on actual edit operations.

c | C[num1],[num2],[destination number]: copy the text starting at line num1 and proceeding through line num2 to, and insert it before the line specified by destination number. If you wish to copy text to the end of the file, give it a number that is greater than the number of lines in your buffer. You will be prompted to confirm the copy operation with a message telling you that you are copying past the current end of the file. The copy command does not update the line pointer.

d | D; d | D[num1]; d | D[num1],[num2]: the delete command with no arguments will delete the "current" line (i.e. your current position within the buffer). With one argument, it will delete the line you have specified. With two line numbers separated by a comma (no spaces), it will delete the text starting at num1 and proceeding through the line specified by num2. The delete command will not update the line pointer, unless you have shrunken the file buffer to a point below that of the line pointer, at which point it will be set to the current last line.

e | E: exits, saving any text changed since the last save of the file buffer. If no text has been changed, it will exit without saving text. The original file will be backed up to a file in the same directory with the same filename, but with a different extension - namely, the ".bak" extension. If the backup exists under that name, it will be silently replaced.

i | I; i | I[num]: insert text before either the "current line" (no arguments), or before the line specified by num. If you wish to append text to the end of the file, use the "a" command, as line numbers out of range of the file will produce an error. Note that the "current" line after this command is executed is whatever you named as the point of insertion.

l | L; l | L[num1]; l | L[num1],[num2]: with no arguments, list the entire file (with no paging). With one argument, list the line specified by num1. With two arguments, list the file's contents starting at the line specified by num1 and proceeding through num2. The line pointer will be set to the last line listed.

m | M[num1],[num2],[destination number]: move the text starting at line num1 and proceeding through line num2 to, and insert it before the line specified by destination number. The text you are moving will be deleted from its original position. If you wish to move text to the end of the file, give it a number that is greater than the number of lines in your buffer. You will be prompted to confirm the move operation with a message telling you that you are copying past the current end of the file. The move command does not update the line pointer. 

n | N: print the current line number.

p | P; p | P[num1]; p | P[num1],[num2]: with no arguments, list the entire file (with paging). At each page, you may choose to continue paging by hitting <ENTER>, or you may quit by hitting <q> or <Q>, followed by <ENTER>. With one argument, list the line specified by num1. With two arguments, list the file's contents (with paging) starting at the line specified by num1 and proceeding through num2. The line pointer will be set to the last line listed.

q | Q; quit, saving no changes since last write. If the file has been changed, you will be prompted in case you wish to abort your "quit" and save your changes.

r | R[num1],[num2 | ?],[searchstring]^[replacestring]: search for searchstring, starting at the line specified by num1 and proceeding through num2 (if present), and replace the text described by searchstring with replacestring. If the second argument is "?" (instead of num2), you will be prompted if you want to do the replacement until all of the possible replacements have been queried. The replace command will not update the line pointer.

s | S[num1],[num2 | ?],[searchstring]: search for searchstring, starting at the line specified by num1 and proceeding through num2 (if present. If the second argument is "?" (instead of num2), you will be prompted if this is the correct match. If a match is found, the line pointer will be updated to the line where the match was found.

t | T[num],[filename]: insert the contents of filename above the line specified by num. If you wish to append the contents of the file being merged to the current file contents, specify a line number that is greater than the current number of lines in the file. You will be prompted, in that case, to proceed (or not) with the transfer. The line pointer will not be changed as a result of this command.

w | W: write the contents of the file buffer to a file on disk. The original file will be backed up as for the exit command (e).

Running the Tool:


This tool takes as input a directory of WiX (v2), CMI, or INF files
and produces a file that lists all the conflicts between their
registry entries.  The file it gives back contains a list of conflicts
and the summed total conflicts between each pair of WiX files.  It
expects the files to have the extension .wxs, .man, or .inf. The tool
can be called as

./AppReader.exe file | -d directory

Note that it does not do a recursive walk of the directory tree
(trivial to add, but I just haven't done it); all the files must be at
the top level of the directory at which you point it.


Output Format:


The conflict lines look like:

C: <registry key name>: <number of conflicting wxs files>
   <app number> writes <reg value>
   .
   .
   .


The app numbers are to save space: there is a name table at the end of
the file that gives the mapping from number to app.  Note that if
there is a conflict on a key/value pair, every app that writes to that
key is listed, even if most of them do not conflict.

After the conflict listings, there is a list with three columns.  The
columns, in order, are <App 1 Number>, <App 2 Number>, and <Number of
conflicts>.  


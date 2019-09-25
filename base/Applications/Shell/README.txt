Scripting Documentation 
-----------------------
This document provides a brief introduction to the script facilities of the shell.


Command line arguments
----------------------
Variables can be passed to a script from the command line and accessed with
$num where num is the number of the shell script variable. The number of
command line variables is given by the $# variable.


Comments
--------
Text following a # on a line is deemed a comment.


Data types
----------
At the moment, the shell only supports primitive types such as integers, booleans, and strings.


Variables
---------
Variables can be assigned to with a simple assignment construct.
For instance, a = 'bc' assigns the string 'bc' to the variable a.
Variables can be referenced by preceding the name with $ (e.q. echo $a)
or with ${name} to separate the reference from surround text such as
b = "surrounding${var}text". References to variables that have not been
previously assigned are considered an error. An error message is printed
and script execution is halted.


Operators
---------

integer: *, / , %, +, -
string: . (concatenation)
boolean: ||, &&, !
comparison: <, <=, ==, >=, >. 

The integer operations coerce the
operand types to ints. Therefore, "5" + "9" will call
Int32.ParseInt() on both of these arguments. If one of the operands
to an integer operator is boolean than true is converted to 1
and false is converted to 0.

String operators will call ToString on the value for an operand.

Boolean operators: coerce operand types to booleans. In the case
of integers, an integer equal to 0 is false while all other values
are equivalent to true. For strings, a value is only coercible
if it is either one of Boolean.TrueString (true) or Boolean.FalseString (false)
(case-insensitive). 


Comparison:
Currently, comparison operators coerce both operands to the type of the left operand
using the methods described thus far. 
Stricter and more sensible typing may be implemented in the future.


Expressions
-----------
Expressions can be constructed from variables, any of the basic primitive
types and the set of operators. 


Control Flow
------------
Language currently supports if, if-else, and while. The conditions to these constructs
are arbitrary expressions that successfully evaluate to a boolean value. Bracing of the statements
for these constructs is required to eliminate ambiguity.


Commands
--------
Unfortunately, commands currently consist of a sequence of alpha-numeric words, a string
literal, interpolation, or integer ending in a new line. Therefore and non-alpha-numeric characters (i.e. %)
must be either placed in a string or interpolation. Hopefully, this will eventually change.


Exit and Exit codes
-----------
The exit status of the last command is given by the $? variable.
The built-in exit command takes optionally one integer argument indicating
the exit code of the script execution. If no argument is specified, the status
of the last executed command is returned. If no argument is given and no
commands have been executed, then 0 is returned. This exit builtin differs from
that of the shell prompt. That version performs a shutdown while this
exits the script.



Grammar
-------
SCRIPT => STMT_LIST

STMT_LIST => STMT
	| STMT STMT_LIST

STMT => while( E ) { STMT_LIST }
	| if( E ) { STMT_LIST }
	| if( E ) { STMT_LIST } else { STMT_LIST }
	| var = E newline


E => integer_literal | string_literal | bool_literal | variable_reference | interpolation 
    | E + E | E - E | E * E | E % E |
    | E < E | E <= E | E == E | E >= E | E > E
    | E . E 
    | E && E | E || E | !E


COMMAND_LINE=> COMMAND_LIST newline

COMMAND_LIST => COM
	| COM COMMAND_LIST

COM =>  word
	| variable_reference
	| integer_literal
	| string_literal
        | interpolation

Example (test script from Shell.sg )
------------------------------------
echo $2 #echo second argument
decho $2
echo number of arguments '=' $#
decho number of arguments '=' $#
				
echo last command exit code '=' $?
decho last command exit code '=' $?
if (true) {
	variable = false
	if ($variable) { 
		var2 = true
		echo broken conditional 
		decho broken conditional 
	} 
	else { 
		var2 = true
		output1 = "bet${variable}ween"
		echo $output1
		decho $output1
	}
	#some comments #
	#
	decho var2 is $var2
	add = -2 + 4
	echo '-2 + 4 =' $add
	decho '-2 + 4 =' $add

	mod = 6 % 5
	echo '6 % 5 =' $mod
	decho '6 % 5 =' $mod

	div = 10 / 5
	echo '10 / 5 =' $div
	decho '10 / 5 =' $div
					
	mult = 2 * 5
	echo '2 * 5=' $mult
	decho '2 * 5=' $mult
				
	var1 = 5
	var2 = 6
					
	if($var1 < $var2){ 
		decho $var1 is less than $var2  
		two = 1
		power = 10
		echo starting loop
		decho starting loop
		while($power > 0){
			two = $(two) * 2
			power = $power - 1
		}
		output2 = "2^10 = $two"
		echo $output2
		decho $output2
	}
	if ($var1 > $var2) {
		echo $var2 is less than $var1
		decho $var2 is less than $var1 
	}
	else {
		output3 = 'var1' . " is " . $var1
		echo $output3
		decho $output3
	}
	var = "test"
	if ("test" == $var) {
		echo string compare success
		decho string compare success
	}	 
}
This directory contains experimental verified OS code.

The build process requires PowerShell.
(included with Windows 7, or downloadable separately)

The build process uses PowerShell scripts, so script execution must be enabled.
(For example, launch "powershell.exe -ExecutionPolicy RemoteSigned".)

To build from a PowerShell prompt, simply type:

  .\build

This will build all tools, run all verification, and compile the
code to two ISO images in the "bin" directory.

(Note: the TAL verification is only performed in the presence of a TAL checker,
which is not part of this distribution.)


NOTES:

BoogieAsm, our BoogiePL-to-MASM translator, enforces on the
following variable name conventions, where x and X represent any sequence of
letters, digits, and underscores, whose first non-underscore character is a
lower-case letter (for x) or uppercase letter (for X):
  - X is a physical global variable, of type int, or a procedure name
  - x is a physical local variable, of type int, or an inline procedure name
  - $X is a ghost variable, of any type, which the untrusted code may read
  - $x is a ghost variable, of any type, which the untrusted code may read/write
  - ?X is an integer constant
  - ?x is a const variable containing an integer constant
The translator signals an error if the untrusted code tries to write to
$X, ?x or ?X.  Note that pure function names and pure function parameters are not
bound by these naming conventions.


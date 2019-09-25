open Microsoft.FSharp.Math

type reg = Eax | Ebx | Ecx | Edx | Esi | Edi | Ebp | Esp

type con = string

type exp =
| EReg of reg
| EConst of bigint
| EOp of exp list
| EApply of string * exp list
| EQuant of string list * exp list

type operand =
| OConst of con
| OReg of reg
| OVar of (bool * string) (* true ==> global, false ==> local *)
| OOffset of reg * con
| OIndex of reg * con * reg * con
| OExp

type cmp = Eq | Ne | Le | Lt | Ge | Gt

type stmt =
| SNone
| SLabel of string
| SGoto of string
| SReturn
| SIReturn
| SIf of cmp * operand * operand * string
| SInline of string
| SCall of string
| SIns of string * operand list * operand list

type block = stmt list

type decl =
| DVar of string
| DFunDecl of string
| DFunDef of string * (string list) * exp
| DInline of string * (string list) * block
| DProc of string * (string list) * block

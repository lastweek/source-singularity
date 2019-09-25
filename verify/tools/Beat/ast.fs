type id = string
type loc = int
type bigint = Microsoft.FSharp.Math.bigint

type btyp =
| BInt | BBool
| BArray of btyp list * btyp
| BNamedType of id

type buop = 
| BNot | BNeg | BOld

type bbop =
| BEquiv | BImply | BAnd | BOr
| BEq | BNe | BLt | BGt | BLe | BGe
| BAdd | BSub | BMul | BDiv | BMod
| BAddChecked | BSubChecked

type bquant =
| BForall | BExists

type bformal_typ =
| BFormalType of btyp
| BFormalAlias of id

type bformal_var = id * bformal_typ
type bformal = id * btyp

type bexp =
| BLoc of loc * bexp
| BVar of id
| BIntConst of bigint
| BBoolConst of bool
| BUop of buop * bexp
| BBop of bbop * bexp * bexp
| BQuant of bquant * bformal list * bexp list * bexp
| BSubscript of bexp * bexp list
| BUpdate of bexp * bexp list * bexp
| BApply of id * bexp list

type bformal_fun = id * btyp * bexp option

type bstmt =
| BLocalDecl of id * bformal_typ * bexp option
| BLabel of id
| BGoto of id
| BAssign of id * bexp
| BIf of bexp * bblock * bblock option
| BWhile of bexp * (loc * bexp) list * bblock
| BAssume of bexp
| BAssert of bexp
| BHavoc of bexp
| BCall of id list * id * bexp list
| BReturn
and bblock = (loc * bstmt) list

type bspec =
| BRequires of bexp
| BEnsures of bexp
| BModifies of id list
| BReturns of bformal list

type proc_kind = Procedure | Implementation

type fun_decl = id * bformal_fun list * btyp * bexp option
type proc_decl = id * bformal_var list * (loc * bspec) list * bblock option * proc_kind

type bdecl =
| BGlobalDecl of id * btyp
| BGlobalAliasDecl of id * (id * btyp) list
| BConstDecl of id * btyp
| BAxiomDecl of bexp
| BTypeDecl of id
| BFunDecl of fun_decl
| BProcDecl of proc_decl

type bdecls = (loc * bdecl) list

open Ast
open Parse
open Parse_util
open Microsoft.FSharp.Compatibility.OCaml.Big_int;;

type env =
  {
    fun_decls:Map<id,loc * fun_decl>;
    proc_decls:Map<id,loc * proc_decl>;
    global_alias_decls:Map<id,(id * btyp) list>;
  }

let build_env decls:env =
  List.fold_left
    (fun env (l, decl) ->
      match decl with
      | BFunDecl ((x, _, _, _) as d) -> {env with fun_decls = env.fun_decls.Add(x, (l, d))}
      | BProcDecl ((x, _, _, _, _) as d) -> {env with proc_decls = env.proc_decls.Add(x, (l, d))}
      | BGlobalAliasDecl (x, ys) -> {env with global_alias_decls = env.global_alias_decls.Add(x, ys)}
      | _ -> env)
    {fun_decls = new Map<id,loc * fun_decl>([]);
     proc_decls = new Map<id,loc * proc_decl>([]);
     global_alias_decls = new Map<id,(id * btyp) list>([]);}
    decls

(*****************************************************************************)

let rec map_exp (f:bexp -> bexp option) (e:bexp):bexp =
  match (f e) with
  | Some e -> e
  | None ->
    (
      let r = map_exp f in
      match e with
      | BLoc (l, e) -> BLoc (l, r e)
      | BVar x -> BVar x
      | BIntConst _ -> e
      | BBoolConst _ -> e
      | BUop (op, e) -> BUop (op, r e)
      | BBop (op, e1, e2) -> BBop (op, r e1, r e2)
      | BQuant (q, fs, ts, e) -> BQuant (q, fs, List.map r ts, r e)
      | BSubscript (e, es) -> BSubscript (r e, List.map r es)
      | BUpdate (e, es, ee) -> BUpdate (r e, List.map r es, r ee)
      | BApply (x, es) -> BApply (x, List.map r es)
    )

let rec map_stmt (fe:bexp -> bexp) (fs:bstmt -> bstmt option) (l:loc, s:bstmt):(loc * bstmt) =
  match fs s with
  | Some s -> (l, s)
  | None ->
    (
      match s with
      | BLocalDecl (x, t, None) -> (l, s)
      | BLocalDecl (x, t, Some e) -> (l, BLocalDecl (x, t, Some (fe e)))
      | BLabel x -> (l, s)
      | BGoto x -> (l, s)
      | BAssign (x, e) -> (l, BAssign (x, fe e))
      | BIf (e, b1, None) -> (l, BIf (fe e, map_block fe fs b1, None))
      | BIf (e, b1, Some b2) -> (l, BIf (fe e, map_block fe fs b1, Some (map_block fe fs b2)))
      | BWhile (e, invs, b) ->
          (l, BWhile (
            fe e,
            List.map (fun (l, e) -> (l, fe e)) invs,
            map_block fe fs b))
      | BAssume e -> (l, BAssume (fe e))
      | BAssert e -> (l, BAssert (fe e))
      | BHavoc e -> (l, BHavoc (fe e))
      | BCall (xs, f, es) -> (l, BCall (xs, f, List.map (fe) es))
      | BReturn -> (l, s)
    )
and map_block (fe:bexp -> bexp) (fs:bstmt -> bstmt option) (b:bblock):bblock = List.map (map_stmt fe fs) b

let map_spec (fe:bexp -> bexp) (l:loc, s:bspec):(loc * bspec) =
  match s with
  | BRequires e -> (l, BRequires (fe e))
  | BEnsures e -> (l, BEnsures (fe e))
  | BModifies xs -> (l, s)
  | BReturns fs -> (l, s)

let subst_id (m:Map<id,bexp>) (x:id):id =
  if (m.ContainsKey(x)) then
    match m.[x] with
    | BVar y -> y
    | _ -> err "internal substitution error"
  else x

(* TODO: capture-avoiding substitution *)
let rec subst_exp (m:Map<id,bexp>) (e:bexp):bexp =
  map_exp
    (fun e ->
      match e with
      | BVar x when m.ContainsKey(x) -> Some (m.[x])
      | _ -> None)
    e

let rec subst_stmt (m:Map<id,bexp>) (l:loc, s:bstmt):(loc * bstmt) =
  map_stmt
    (subst_exp m)
    (fun s ->
      match s with
      | BAssign (x, e) ->
          Some (BAssign (subst_id m x, subst_exp m e))
      | BCall (xs, f, es) ->
          Some (BCall (List.map (subst_id m) xs, f, List.map (subst_exp m) es))
      | _ -> None)
    (l, s)

let subst_block (m:Map<id,bexp>) (b:bblock):bblock = List.map (subst_stmt m) b

let subst_spec (m:Map<id,bexp>) (l:loc, s:bspec):(loc * bspec) =
  map_spec (subst_exp m) (l, s)

(*****************************************************************************)

let id_is_reg (x:id) =
  match x with "eax" | "ebx" | "ecx" | "edx" | "esi" | "edi" | "ebp" | "esp" -> true | _ -> false

let id_is_ghost (x:id) = x.[0] == '$'

type procKind = PIns | PInline | PProc

let proc_kind (x:id):procKind =
  let rec f i =
    match x.[i] with
    | '_' -> f (i + 1)
    | c when System.Char.IsLower(c) -> PInline
    | c when System.Char.IsUpper(c) -> PProc
    | _ -> err ("bad procedure name: " + x) in
  match x with
  | "Mov" | "Not" | "Add" | "AddChecked" | "Sub" | "SubChecked"
  | "Mul" | "MulChecked" | "Div" | "And" | "Or" | "Xor" | "Shl" | "Shr"
  | "Lea" | "LeaUnchecked" | "LeaSignedIndex"
  | "RoLoadU8" | "RoLoadS8" | "RoLoadU16" | "RoLoadS16" | "RoLoad32"
  | "Load" | "SectionLoad"
  | "Store" | "SectionStore" | "VgaTextStore16" | "VgaDebugStore16" | "IdtStore"
  | "IomStore" | "IomRegLoad" | "IomRegStore"
  | "PciConfigAddrOut32" | "PciConfigDataIn32" | "PciConfigDataOut32"
  | "PciMemLoad32" | "PciMemStore32"
  | "Lidt"
  | "KeyboardStatusIn8" | "KeyboardDataIn8"
  | "PicOut8" | "PitModeOut8" | "PitFreqOut8"
  | "Rdtsc"
      -> PIns
  | _ -> f 0

let expand_deep_conjuncts = ref true;

let rec list_of_conjuncts (env:env) (depth:int) (lBase:loc) (l:loc) (e:bexp):(loc * bexp) list =
  let lb = 100000 * lBase + l in
  let ll = if l = lBase then l else lb in
  if depth = 0 then [(ll, e)] else
  let f0 = list_of_conjuncts env (depth - 0) lBase in
  let f1 = list_of_conjuncts env (depth - 1) lBase in
  match e with
    | BLoc (lAnd, BBop (BAnd, e1, e2)) ->
        (f0 l e1) @ (f1 lAnd e2)
    | BApply (x, es) when env.fun_decls.ContainsKey(x) ->
      (
        let (lf, (_, fs, _, ee)) = env.fun_decls.[x] in
        match ee with
        | None -> [(lb, e)]
        | Some ee ->
            let m = List.map2 (fun (x, _, _) e -> (x, e)) fs es in
            let s = new Map<id,bexp>(m)
            f0 lf (subst_exp s ee)
      )
    | BBop (BImply, e1, e2) when !expand_deep_conjuncts ->
        List.map (fun (l, e) -> (l, BBop (BImply, e1, e))) (f0 l e2)
    | BQuant (q, fs, ts, e) when !expand_deep_conjuncts ->
        List.map (fun (l, e) -> (l, BQuant (q, fs, ts, e))) (f0 l e)
    | _ -> [(lb, e)]

let rec expand_conjuncts_stmt (env:env) (depth:int) (l:loc, s:bstmt):(loc * bstmt) list =
  let f = expand_conjuncts_block env depth in
  match s with
  | BIf (e, b1, b2) -> [(l, BIf (e, f b1, match b2 with None -> None | Some b2 -> Some (f b2)))]
  | BWhile (e, invs, b) ->
      let invs = List.flatten (List.map (fun (l, e) -> list_of_conjuncts env depth l l e) invs) in
      [(l, BWhile (e, invs, f b))]
  | BAssert e -> List.map (fun (l, e) -> (l, BAssert e)) (list_of_conjuncts env depth l l e)
  | _ -> [(l, s)]
and expand_conjuncts_block (env:env) (depth:int) (b:bblock):bblock =
  List.flatten (List.map (expand_conjuncts_stmt env depth) b)

let expand_conjuncts_spec (env:env) (depth:int) (l:loc, s:bspec):(loc * bspec) list =
  match s with
  | BRequires e -> List.map (fun (l, e) -> (l, BRequires e)) (list_of_conjuncts env depth l l e)
  | BEnsures e -> List.map (fun (l, e) -> (l, BEnsures e)) (list_of_conjuncts env depth l l e)
  | _ -> [(l, s)]

let expand_conjuncts_decl (env:env) (depth:int) (l:loc, d:bdecl):(loc * bdecl) =
  match d with
  | BProcDecl (x, ps, specs, b, p) ->
      (l, BProcDecl (x, ps,
        List.flatten (List.map (expand_conjuncts_spec env depth) specs),
        (match b with None -> None | Some b -> Some (expand_conjuncts_block env depth b)),
        p))
  | _-> (l, d)

let expand_conjuncts_decls (env:env) (depth:int) = List.map (expand_conjuncts_decl env depth)

(*****************************************************************************)

let rec sep_list (sep:string) (l:string list) =
  match l with
  | [] -> ""
  | [x] -> x
  | h::t -> h + sep + (sep_list sep t)

let rec string_of_btyp t =
  match t with
  | BInt -> "int"
  | BBool -> "bool"
  | BArray (ts, t) -> "[" + (sep_list "," (List.map string_of_btyp ts)) + "]" + (string_of_btyp t)
  | BNamedType x -> x

let string_of_buop op =
  match op with
  | BNot -> "!"
  | BNeg -> "-"
  | BOld -> "old"

let string_of_bbop op =
  match op with
  | BEquiv -> "<==>"
  | BImply -> "==>"
  | BAnd -> "&&"
  | BOr -> "||"
  | BEq -> "=="
  | BNe -> "!="
  | BLt -> "<"
  | BGt -> ">"
  | BLe -> "<="
  | BGe -> ">="
  | BAdd -> "+"
  | BSub -> "-"
  | BMul -> "*"
  | BDiv -> "/"
  | BMod -> "%"
  | BAddChecked -> "$+"
  | BSubChecked -> "$-"

let string_of_bquant q =
  match q with
  | BForall -> "forall"
  | BExists -> "exists"

let string_of_bformal (x, t) = x + ":" + (string_of_btyp t)
let string_of_bformal_fun (x, t, _) = x + ":" + (string_of_btyp t)

let string_of_bformal_var (x, t) =
  match t with
  | BFormalType t -> x + ":" + (string_of_btyp t)
  | BFormalAlias t -> err ("unexpected alias " ^ x ^ " " ^ t)

let prec_of_uop op = match op with | BNot -> 50 | BNeg -> 50 | BOld -> 99
let prec_of_bop op =
  match op with
  | BEquiv -> 10 | BImply -> 10
  | BAnd -> 15 | BOr -> 15
  | BEq -> 20 | BNe -> 20 | BLt -> 20 | BGt -> 20 | BLe -> 20 | BGe -> 20
  | BAdd -> 30 | BSub -> 30 | BAddChecked -> 30 | BSubChecked -> 30
  | BMul -> 35 | BDiv -> 35 | BMod -> 35

let rec string_of_bexp prec e =
  let (s, ePrec) =
    match e with
    | BLoc (_, e) -> (string_of_bexp prec e, 99)
    | BVar x when id_is_ghost x -> (x, -5)
    | BVar x -> (x, 99)
    | BIntConst i -> (string i, 99)
    | BBoolConst true -> ("true", 99)
    | BBoolConst false -> ("false", 99)
    | BUop (op, e) -> let ep = prec_of_uop op in ((string_of_buop op) + (string_of_bexp (ep + 1) e), ep)
    | BBop (op, e1, e2) ->
        let ep = prec_of_bop op in
        let (epLeft, epRight) =
          match op with
          | BAdd | BSub | BMul | BDiv | BMod | BAddChecked | BSubChecked -> (ep, ep + 1)
          | _ -> (ep + 1, ep + 1)
        ((string_of_bexp epLeft e1) + (string_of_bbop op) + (string_of_bexp epRight e2), ep)
    | BQuant (q, fs, ts, e) ->
      (   (string_of_bquant q) + " "
        + (sep_list "," (List.map string_of_bformal fs))
        + "::"
        + (match ts with [] -> "" | _ -> "{"+ (sep_list "," (List.map (string_of_bexp 5) ts)) + "}")
        + (string_of_bexp 6 e),
          (-5)
      )
    | BSubscript (e, es) -> ((string_of_bexp 90 e) + "[" + (sep_list "," (List.map (string_of_bexp 5) es)) + "]", 40)
    | BUpdate (e, es, ee) -> ((string_of_bexp 90 e) + "[" + (sep_list "," (List.map (string_of_bexp 90) es)) + ":=" + (string_of_bexp 90 ee) + "]", 40)
    | BApply (x, es) -> (x + "(" + (sep_list "," (List.map (string_of_bexp 5) es)) + ")", 90)
  in if prec <= ePrec then s else "(" + s + ")"

type print_state =
  {
    print_out:System.IO.TextWriter;
    indent:string;
    cur_line:int ref;
  }
  member this.PrintLine (s:string) = incr this.cur_line; this.print_out.WriteLine (this.indent + s)
  member this.SetLine (i:int) =
    if i = !this.cur_line then ()
    else if i < !this.cur_line || i > !this.cur_line + 8 then this.cur_line := i; this.print_out.WriteLine ("#line " + (string i))
    else this.PrintLine ""; this.SetLine i

let rec print_bstmt (state:print_state) (l:loc, s) =
  let () = state.SetLine l in
  let p:(string -> unit) = state.PrintLine in
  match s with
  | BLocalDecl (x, t, None) -> p ("var " + (string_of_bformal_var (x, t)) + ";")
  | BLocalDecl (x, t, Some e) -> p ("var " + (string_of_bformal_var (x, t)) + "=" + (string_of_bexp 0 e) + ";")
  | BLabel x -> p (x + ":")
  | BGoto x -> p ("goto " + x + ";")
  | BAssign (x, e) -> p (x + ":=" + (string_of_bexp 0 e) + ";")
  | BIf (e, b1, b2) ->
    (
      p ("if(" + (string_of_bexp 0 e) + ")");
      print_bblock state b1;
      (match b2 with None -> () | Some b -> print_bblock state b)
    )
  | BWhile (e, invs, b) ->
    (
      p ("while(" + (string_of_bexp 0 e) + ")");
      List.iter (fun (l:loc, e) -> state.SetLine l; p ("invariant " + (string_of_bexp 0 e))) invs;
      print_bblock state b
    )
  | BAssume e -> p ("assume " + (string_of_bexp 0 e) + ";")
  | BAssert e -> p ("assert " + (string_of_bexp 0 e) + ";")
  | BHavoc e -> p ("havoc " + (string_of_bexp (-5) e) + ";")
  | BCall ([], f, es) -> p ("call " +                           f + "(" + (sep_list "," (List.map (string_of_bexp 5) es)) + ");")
  | BCall (xs, f, es) -> p ("call " + (sep_list "," xs)+ ":=" + f + "(" + (sep_list "," (List.map (string_of_bexp 5) es)) + ");")
  | BReturn -> p "return;"
and print_bblock (state:print_state) b =
  state.PrintLine "{";
  List.iter (print_bstmt {state with indent = "  " + state.indent}) b;
  state.PrintLine "}"

let print_bspec (state:print_state) (l:loc, s) =
  let () = state.SetLine l in
  let p:(string -> unit) = state.PrintLine in
  match s with
  | BRequires e -> p ("requires " + (string_of_bexp 0 e) + ";")
  | BEnsures e -> p ("ensures " + (string_of_bexp 0 e) + ";")
  | BModifies [] -> ()
  | BModifies xs -> p ("modifies " + (sep_list "," xs) + ";")
  | BReturns fs -> p ("returns(" + (sep_list "," (List.map string_of_bformal fs)) + ")")

let string_of_procimpl p = match p with Procedure -> "procedure" | Implementation -> "implementation"

let print_bdecl (state:print_state) (l:loc, decl) =
  let () = state.SetLine l in
  let p:(string -> unit) = state.PrintLine in
  match decl with
  | BGlobalDecl (x, t) -> p ("var " + x + ":" + (string_of_btyp t) + ";")
  | BGlobalAliasDecl (x, ys) -> ()
  | BConstDecl (x, t) -> p ("const " + x + ":" + (string_of_btyp t) + ";")
  | BAxiomDecl e -> p ("axiom " + (string_of_bexp 0 e) + ";")
  | BTypeDecl x -> p ("type " + x + ";")
  | BFunDecl (x, ps, t, e) ->
    (
      p ("function " + x + "(" + (sep_list "," (List.map string_of_bformal_fun ps)) + ")");
      p ("  returns(" + (string_of_btyp t) + ")");
      (match e with
          None -> p ";"
        | Some e ->
          (
            p ("{");
            p ("  " + (string_of_bexp 0 e));
            p ("}")
          )
      )
    )
  | BProcDecl (x, ps, (l, BReturns fs)::specs, None, pi) ->
    (
      p ((string_of_procimpl pi) + " " + x + "(" + (sep_list "," (List.map string_of_bformal_var ps)) + ")")
      print_bspec state (l, BReturns fs);
      p ";"
      List.iter (print_bspec state) specs;
    )
  | BProcDecl (x, ps, specs, b, pi) ->
    (
      p ((string_of_procimpl pi) + " " + x + "(" + (sep_list "," (List.map string_of_bformal_var ps)) + ")"
        + (match b with None -> ";" | _ -> ""));
      List.iter (print_bspec state) specs;
      (match b with None -> () | Some b -> print_bblock state b)
    )

let print_bdecls (state:print_state) decls = List.iter (print_bdecl state) decls

(*****************************************************************************)

let eax = "eax"
let eaxVar = BVar "eax"

let exp_is_reg (e:bexp) =
  match e with BVar x when id_is_reg x -> true | _ -> false

let exp_is_const (e:bexp) =
  match e with BIntConst _ -> true | _ -> false

let exp_is_reg_or_const (e:bexp) = (exp_is_reg e) || (exp_is_const e)

let exp_is_var (e:bexp) =
  match e with BVar x -> true | _ -> false

let exp_is_var_or_const (e:bexp) = (exp_is_var e) || (exp_is_const e)

let exps_for_x86 (e1:bexp) (e2:bexp):bool =
      ((exp_is_var e1) && (exp_is_reg_or_const e2))
   || ((exp_is_var e2) && (exp_is_reg_or_const e1))

let negate_comparison_op (op:bbop):bbop =
  match op with
  | BEq -> BNe
  | BNe -> BEq
  | BLt -> BGe
  | BGt -> BLe
  | BLe -> BGt
  | BGe -> BLt
  | _ -> err "conditional expression must be a comparison expression"

let get_comparison_exp (e:bexp):(bbop * bexp * bexp) =
  match e with
  | BBop (op, e1, e2) -> (op, e1, e2)
  | _ -> err "conditional expression must be a comparison expression"

let new_label:unit->id =
  let nextLabel = ref 0 in
  fun () -> incr nextLabel; "__L" + (string !nextLabel)

let add_local (locals:(id * bformal_typ) list ref) (x:id) (t:bformal_typ):unit =
  if not (List.mem_assoc x !locals) then locals := (x, t)::(!locals);

let tmp_var (i:int):id = "__tmp" + (string i)

let get_tmp_var (locals:(id * bformal_typ) list ref) (i:int):id =
  let x = tmp_var i in
  add_local locals x (BFormalType BInt);
  x

let global_param_name (f:id) (p:id) = "__" + f + "$" + p

let rec compile_exp (locals:(id * bformal_typ) list ref) (l:loc) (dest:id) (temp:int) (e:bexp):(loc * bstmt) list =
  let er () = err ("cannot compile expression " + (string_of_bexp 0 e) + " at line " + (string l)) in
  match e with
  | BLoc (_, e) -> compile_exp locals l dest temp e
  | BVar x -> if dest = x then [] else [(l, BAssign (dest, e))]
  | BIntConst i -> [(l, BAssign (dest, e))]
  | BBop (op, ((BVar x1) as e1), e2) when dest = x1 && exps_for_x86 e1 e2 ->
    ( match op with
      | BAdd        -> [(l, BCall ([dest], "Add",        [e1; e2]))]
      | BSub        -> [(l, BCall ([dest], "Sub",        [e1; e2]))]
      | BAddChecked -> [(l, BCall ([dest], "AddChecked", [e1; e2]))]
      | BSubChecked -> [(l, BCall ([dest], "SubChecked", [e1; e2]))]
      //| BMul
      //| BDiv
      //| BMod
      | _ -> er ()
    )
  | BBop (op, ((BVar x1) as e1), e2) when dest = x1 ->
      (compile_exp locals l eax  (temp + 0) e2) @
      (compile_exp locals l dest (temp + 0) (BBop (op, e1, eaxVar)))
  | BBop (op, e1, e2) when exp_is_var_or_const e2 ->
      (compile_exp locals l eax  (temp + 0) e1) @
      (compile_exp locals l eax  (temp + 0) (BBop (op, eaxVar, e2))) @
      (compile_exp locals l dest (temp + 0) eaxVar)
  | BBop (op, e1, e2) ->
      let x = get_tmp_var locals temp in
      (compile_exp locals l x    (temp + 1) e2) @
      (compile_exp locals l eax  (temp + 1) e1) @
      (compile_exp locals l dest (temp + 0) (BBop (op, eaxVar, BVar x)))
  | _ -> er ()

let compile_comparison (locals:(id * bformal_typ) list ref) (l:loc) (e:bexp):(bbop * bexp * bexp * (loc * bstmt) list) =
  let (op, e1, e2) = get_comparison_exp e in
  if (exps_for_x86 e1 e2) then (op, e1, e2, [])
  else if (exp_is_var_or_const e1) then (op, e1, eaxVar, compile_exp locals l eax 0 e2)
  else if (exp_is_var_or_const e2) then (op, eaxVar, e2, compile_exp locals l eax 0 e1)
  else
  (
    let x = get_tmp_var locals 0 in
    (op, BVar x, eaxVar,
      (compile_exp locals l eax 0 e1) @
      (compile_exp locals l x   0 eaxVar) @
      (compile_exp locals l eax 0 e2))
  )

let rec compile_stmt (env:env) (locals:(id * bformal_typ) list ref) (l:loc, s:bstmt):(loc * bstmt) list =
  match s with
  | BLocalDecl (x, t, None) -> add_local locals x t; []
  | BLocalDecl (x, t, Some e) -> add_local locals x t; compile_stmt env locals (l, BAssign (x, e))
  | BLabel x -> [(l, s)]
  | BGoto x -> [(l, s)]
  | BAssign (x, e) when id_is_ghost x -> [(l, s)]
  | BAssign (x, e) -> compile_exp locals l x 0 e
  | BIf (e, [(lg, BGoto target)], None) ->
    (
      let (op, e1, e2, ss) = compile_comparison locals l e in
      ( ss @
        [(l, BIf (BBop (op, e1, e2), [(lg, BGoto target)], None))]
      )
    )
  | BIf (e, b1, None) ->
    (
      let (op, e1, e2, ss) = compile_comparison locals l e in
      let l1 = new_label () in
      ( ss @
        [(l, BIf (BBop (negate_comparison_op op, e1, e2), [(l, BGoto l1)], None))] @
        (compile_block env locals b1) @
        [(l, BLabel l1)]
      )
    )
  | BIf (e, b1, Some b2) ->
    (
      let (op, e1, e2, ss) = compile_comparison locals l e in
      let l1 = new_label () in
      let l2 = new_label () in
      ( ss @
        [(l, BIf (BBop (negate_comparison_op op, e1, e2), [(l, BGoto l1)], None))] @
        (compile_block env locals b1) @
        [(l, BGoto l2)] @
        [(l, BLabel l1)] @
        (compile_block env locals b2) @
        [(l, BLabel l2)]
      )
    )
  | BWhile (e, invs, b) ->
    (
      let (op, e1, e2, ss) = compile_comparison locals l e in
      let l1 = new_label () in
      let l2 = new_label () in
      ( [(l, BLabel l1)] @
        (List.map (fun (l, e) -> (l, BAssert e)) invs) @
        ss @
        [(l, BIf (BBop (negate_comparison_op op, e1, e2), [(l, BGoto l2)], None))] @
        (compile_block env locals b) @
        [(l, BGoto l1)] @
        [(l, BLabel l2)]
      )
    )
  | BAssume e -> [(l, s)]
  | BAssert e -> [(l, s)]
  | BHavoc e -> [(l, s)]
  | BCall (xs, p, es) ->
      if not (env.proc_decls.ContainsKey p) then [(l, BCall (xs, p, es))] else
      let (_, (_, ps, specs, b, _)) = env.proc_decls.[p] in
      let ps = List.filter (fun (_, t) -> match t with BFormalType _ -> true | _ -> false) ps in
      let xes = List.map2 (fun (x, t) e -> (x, e)) ps es in
      let (gps, rps) = List.partition (fun (x, e) -> id_is_ghost x) xes in
      let assigns =
        List.flatten
          (List.map
            (fun (x, e) -> compile_stmt env locals (l, BAssign (global_param_name p x, e)))
            rps) in
      assigns @ [(l, BCall (xs, p, List.map snd gps))]
  | BReturn -> [(l, s)]

and embellish_stmts (b:bblock):bblock =
  match b with
  | [] -> []
  // TODO: don't hard-wire so many cases in:
  | (l, BCall ([x1], "GcLoad", [a1]))::t -> (l, BCall ([], "gcLoad", [a1]))::(l, BCall ([x1], "Load", [a1]))::(embellish_stmts t)
  | (l, BCall ([], "GcStore", [a1; a2]))::t -> (l, BCall ([], "gcStore", [a1; a2]))::(l, BCall ([], "Store", [a1; a2]))::(embellish_stmts t)
  | (l, BCall ([x1], "DLoad", [a1]))::t -> (l, BCall ([], "dLoad", [a1]))::(l, BCall ([x1], "Load", [a1]))::(embellish_stmts t)
  | (l, BCall ([], "DStore", [a1; a2]))::t -> (l, BCall ([], "dStore", [a1; a2]))::(l, BCall ([], "Store", [a1; a2]))::(embellish_stmts t)
  | (l, BCall ([x1], "PciLoad", [a1]))::t -> (l, BCall ([], "pciLoad", [a1]))::(l, BCall ([x1], "Load", [a1]))::(embellish_stmts t)
  | (l, BCall ([], "PciStore", [a1; a2]))::t -> (l, BCall ([], "pciStore", [a1; a2]))::(l, BCall ([], "Store", [a1; a2]))::(embellish_stmts t)
  | (l, BCall ([x1], "FLoad", [a1; a2]))::t -> (l, BCall ([], "fLoad", [a1; a2]))::(l, BCall ([x1], "Load", [a2]))::(embellish_stmts t)
  | (l, BCall ([], "FStore", [a1; a2; a3]))::t -> (l, BCall ([], "fStore", [a1; a2; a3]))::(l, BCall ([], "Store", [a2; a3]))::(embellish_stmts t)
  | (l, BCall ([x1], "TLoad", [a1; a2]))::t -> (l, BCall ([], "tLoad", [a1; a2]))::(l, BCall ([x1], "Load", [a2]))::(embellish_stmts t)
  | (l, BCall ([], "TStore", [a1; a2; a3]))::t -> (l, BCall ([], "tStore", [a1; a2; a3]))::(l, BCall ([], "Store", [a2; a3]))::(embellish_stmts t)
  | ((_, BCall ([], "_call", [])) as h1)::((_, BCall ([], "Call", [])) as h2)::h3::t -> h1::h2::h3::(embellish_stmts t)
  | ((_, BCall ([], "Call", [])) as h1)::h2::t -> h1::h2::(embellish_stmts t)
  | ((_, BCall ([], "ret", _)) as h1)::((_, BCall ([], "Ret", _)) as h2)::h3::t -> h1::h2::h3::(embellish_stmts t)
  | ((_, BCall ([], "iret", _)) as h1)::((_, BCall ([], "IRet", _)) as h2)::h3::t -> h1::h2::h3::(embellish_stmts t)
  | ((_, BCall ([], "Ret", _)) as h1)::h2::t -> h1::h2::(embellish_stmts t)
  | ((_, BCall ([], "IRet", _)) as h1)::h2::t -> h1::h2::(embellish_stmts t)
  | ((_, BCall ([], "Go", _)) as h1)::h2::t -> h1::h2::(embellish_stmts t)
  | ((_, BHavoc (BVar "$Eip")) as h1)::h2::t -> h1::h2::(embellish_stmts t)
  | ((l, BCall (_, x, _)) as h)::t when (proc_kind x = PProc) ->
      (l, BCall ([], "_call", []))::(l, BCall ([], "Call", []))::h::(embellish_stmts t)
  | ((l, BReturn) as h)::t ->
      // call _ret(old($Mem), old($sMem), old($dMem), old($pciMem), old($tMems), old($fMems), old($gcMem));
      // call Ret(old($RET));
      // return;
      let h1 = (l, BCall ([], "_ret", [BUop (BOld, BVar "$Mem"); BUop (BOld, BVar "$sMem"); BUop (BOld, BVar "$dMem"); BUop (BOld, BVar "$pciMem"); BUop (BOld, BVar "$tMems"); BUop (BOld, BVar "$fMems"); BUop (BOld, BVar "$gcMem")])) in
      let h2 = (l, BCall ([], "Ret", [BUop (BOld, BVar "$RET")])) in
      h1::h2::h::(embellish_stmts t)
  | ((l, BGoto _) as h)::t ->
      (l, BHavoc (BVar "$Eip"))::h::(embellish_stmts t)
//      (l, BCall ([], "Go", []))::h::(embellish_stmts t)
  | ((l, BIf _) as h)::t ->
      (l, BHavoc (BVar "$Eip"))::h::(embellish_stmts t)
//      (l, BCall ([], "Go", []))::h::(embellish_stmts t)
  | (l, BAssign (x, e))::t when not (id_is_ghost x) -> (l, BCall ([x], "Mov", [e]))::(embellish_stmts t)
  | h::t -> h::(embellish_stmts t)

and compile_block (env:env) (locals:(id * bformal_typ) list ref) (b:bblock):bblock =
  let b = List.flatten (List.map (compile_stmt env locals) b) in
  let b = embellish_stmts b in
  b

let rec aliases_block (m:Map<id,bexp>) (b:bblock):bblock =
  match b with
  | [] -> []
  | ((l, BLocalDecl (x, BFormalAlias y, None)) as s)::ss -> aliases_block (m.Add(x, BVar y)) ss
  | ((l, BLocalDecl (x, BFormalAlias y, Some e)) as s)::ss ->
      (l, BAssign (y, subst_exp m e))::(aliases_block (m.Add(x, BVar y)) ss)
  | (l, BIf (e, s1, None))::ss ->
      (l, BIf (subst_exp m e, aliases_block m s1, None))::(aliases_block m ss)
  | (l, BIf (e, s1, Some s2))::ss ->
      (l, BIf (subst_exp m e, aliases_block m s1, Some (aliases_block m s2)))::(aliases_block m ss)
  | (l, BWhile (e, invs, s))::ss ->
      (l,
        BWhile (subst_exp m e,
          List.map
            (fun (l, e) -> (l, subst_exp m e)) invs, aliases_block m s))::(aliases_block m ss)
  | s::ss -> (subst_stmt m s)::(aliases_block m ss)

let rec global_alias_list (env:env) (to_id:'a -> id option) (from_id:(id * btyp) -> 'a) (l:'a list): 'a list =
  let r = global_alias_list env to_id from_id in
  match l with
  | [] -> []
  | h::t ->
    (
      match to_id h with
      | Some x when env.global_alias_decls.ContainsKey(x) ->
        let ys = env.global_alias_decls.[x] in
        let hs = List.map from_id ys in
        (r hs) @ (r t)
      | _ -> h::(r t)
    )

// Expand global aliases
let rec global_alias_exp (env:env) (e:bexp):bexp =
  map_exp
    (fun e ->
      match e with
      | BApply (x, es) ->
          Some (
            BApply (x,
              global_alias_list env
                (fun a -> match a with BVar y -> Some y | _ -> None)
                (fun (y, _) -> BVar y)
                es))
      | BQuant (q, fs, triggers, e) ->
          let fs = global_alias_list env (fun (x, _) -> Some x) (fun par -> par) fs in
          let e = global_alias_exp env e in
          Some (BQuant (q, fs, triggers, e))
      | _ -> None)
    e

let global_alias_spec (env:env) (l:loc, s:bspec):(loc * bspec) =
  match s with
  | BModifies xs -> (l, BModifies (global_alias_list env (fun x -> Some x) (fun (x, _) -> x) xs))
  | _ -> (l, s)

let global_alias_decl (env:env) (l:loc, d:bdecl):(loc * bdecl) =
  match d with
  | BAxiomDecl e -> (l, BAxiomDecl (global_alias_exp env e))
  | BFunDecl (x, fs, t, eOpt) ->
      let eOpt = match eOpt with None -> None | Some e -> Some (global_alias_exp env e) in
      let fs =
        global_alias_list env
          (fun (x, _, _) -> Some x)
          (fun (x, t) -> (x, t, None))
          fs in
      (l, BFunDecl (x, fs, t, eOpt))
  | BProcDecl (x, ps, specs, None, p) ->
      let specs = List.map (global_alias_spec env) specs in
      let specs = List.map (map_spec (global_alias_exp env)) specs in
      (l, BProcDecl (x, ps, specs, None, p))
  | BProcDecl (x, ps, specs, Some b, p) ->
      let specs = List.map (global_alias_spec env) specs in
      let specs = List.map (map_spec (global_alias_exp env)) specs in
      let b = map_block (global_alias_exp env) (fun s -> None) b in
      (l, BProcDecl (x, ps, specs, Some b, p))
  | _ -> (l, d)

let global_alias_decls (env:env) = List.map (global_alias_decl env)

// Replace missing function arguments with defaults
let fun_defaults_exp (env:env) (e:bexp):bexp =
  map_exp
    (fun e ->
      match e with
      | BApply (x, es) when env.fun_decls.ContainsKey(x) ->
        let (_, (_, ps, _, _)) = env.fun_decls.[x] in
        let rec f ps es =
          match (ps, es) with
          | ([], []) -> []
          | ([], _) -> err ("too many arguments to " + x)
          | ((_, _, None)::_, []) -> err ("missing arguments to " + x)
          | ((_, _, Some e)::ps, []) -> e::(f ps es)
          | (_::ps, e::es) -> e::(f ps es) in
        Some (BApply (x, f ps es))
      | _ -> None)
    e

let compile_decl (env:env) (modify:id list ref) (l:loc, d:bdecl):(loc * bdecl) list =
  match d with
  | BProcDecl (x, ps, specs, None, p) ->
      let specs = List.map (map_spec (fun_defaults_exp env)) specs in
      [(l, BProcDecl (x, ps, specs, None, p))]
  | BProcDecl (x, ps, specs, Some b, p) ->
      let b = map_block (fun_defaults_exp env) (fun s -> None) b in
      let specs = List.map (map_spec (fun_defaults_exp env)) specs in
      let (gps, rps0) = List.partition (fun (x, _) -> id_is_ghost x) ps in
      let (rps, aps) =
        List.fold_left
          (fun (rps, aps) (x, t) ->
            match t with
            | BFormalType t -> ((x, t)::rps, aps)
            | BFormalAlias t -> (rps, (x, t)::aps))
          ([], [])
          rps0 in
      let m =
        new Map<id,bexp>(
            (List.map (fun (xp, _) -> (xp, BVar (global_param_name x xp))) rps)
          @ (List.map (fun (xp, xa) -> (xp, BVar xa)) aps)) in
      let specs = List.map (subst_spec m) specs in
      let b = subst_block m b in
      let locals = ref ([]:(id * bformal_typ) list) in
      let b = aliases_block (new Map<id,bexp>([])) b in
      let b = compile_block env locals b in
      let bLocals = List.map (fun (x, t) -> (l, BLocalDecl (x, t, None))) !locals in
      let mSpec = (l, BModifies (!modify)) in
      let global_vars =
        List.map
          (fun (xp, t) ->
            let name = global_param_name x xp in
            let () = modify := (name::(!modify)) in
            (l, BGlobalDecl (name, t))
          )
          rps in
      global_vars @ [(l, BProcDecl (x, gps, mSpec::specs, Some (bLocals @ b), p))]
  | _ -> [(l, d)]

let compile_decls (env:env) ds = List.flatten (List.map (compile_decl env (ref ([]:id list))) ds)

(*****************************************************************************)

let expand_depth = ref 0
let include_files = ref ([]:string list)

(* Each command-line argument is the name of a lemma *)
let args =
  [ 
    ("-expand"  , Arg.Int    (fun i -> expand_depth := i)  , "Expand formula definitions (for better error messages)")
    ("-i"       , Arg.String (fun s -> include_files := s::(!include_files)), "Include file")
  ]

let main (argv) =
  try
  (
    let cmd_args = System.Environment.GetCommandLineArgs () in
    Arg.parse_argv (ref 0) cmd_args args (fun _ -> ()) "error parsing arguments";

    let parse_file name =
      line := 1;
      Parse.start Lex.token (Lexing.from_channel (open_in name)) in
    let includes = List.map parse_file (!include_files) in

    line := 1;
    let p = Parse.start Lex.token (Lexing.from_channel stdin) in
    let env = build_env ((List.flatten includes) @ p) in
    let (includes2, p) =
      (global_alias_decls env (List.flatten includes), global_alias_decls env p) in
    let env = build_env (includes2 @ p) in
    let p = expand_conjuncts_decls env (!expand_depth) p in
    let p = compile_decls env p in
    let () = print_bdecls { print_out = System.Console.Out; indent = ""; cur_line = ref 1; } p in
    ()
    (*    print_program inlines p; *)
  )
  with
     | Err s -> (print_endline "error:"; print_endline s; exit 1)
     | ParseErr x -> (print_endline ("error near line " + (string !(line))); print_endline x; exit 1)
     | :? System.ArgumentException as x -> (print_endline ("error near line " + (string !(line))); print_endline (x.ToString ()); exit 1)
     | Failure x -> (print_endline ("error near line " + (string !(line))); print_endline x; exit 1)
     | x -> (print_endline (x.ToString ()); exit 1)
;;

let () = main (System.Environment.GetCommandLineArgs ())



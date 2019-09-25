open Ast
open Parse
open Parse_util
open Microsoft.FSharp.Math

let procname (s:string) = "_?" ^ s
let global_var_name (s:string) = "_$$" ^ s
let local_var_name (ctxt:string) (s:string) = "__$" ^ ctxt ^ "$" ^ s
let label (ctxt:string) (s:string) = ctxt ^ "$" ^ s

let sym = ref 0
let gensym () = incr sym; "$$" ^ (string_of_int !sym)

type inlineMap = (string * (unit -> unit)) list

let flat_map f x = List.flatten (List.map f x)
let list_remove x l = List.filter (fun y -> x <> y) l

type width = W8 | W16 | W32
let string_of_width w = match w with W8 -> "byte" | W16 -> "word" | W32 -> "dword"

// Returns list of declarations that e depends on
let rec check_exp (scopeVars:string list) (e:exp):string list =
  match e with
  | EReg _ -> err "register not in scope"
  | EConst _ -> []
  | EOp es -> flat_map (check_exp scopeVars) es
  | EApply (x, es) ->
      let deps = flat_map (check_exp scopeVars) es in
      if (List.mem x scopeVars) then deps else x::deps
  | EQuant (xs, es) -> flat_map (check_exp (xs @ scopeVars)) es

let check_module (scopeVars:string list) (intf:decl list, impl:decl list):string list =
  let check_decl (d:decl):string list * (string * string list) list =
    match d with
    | DFunDecl x -> ([x], [])
    | DFunDef (x, parms, e) -> ([], [x, check_exp (parms @ scopeVars) e])
    | DVar _ -> ([], [])
    | DInline _ -> ([], [])
    | DProc _ -> ([], [])
  let pubs = List.map check_decl intf in
  let prvs = List.map check_decl impl in
  let (pub_decls, pub_defs) = (flat_map fst pubs, flat_map snd pubs) in
  let (prv_decls, prv_defs) = (flat_map fst prvs, flat_map snd prvs) in
  let decls = pub_decls @ prv_decls in
  let defs = pub_defs @ prv_defs in
  let undefs = List.filter (fun d -> not (List.mem_assoc d defs)) decls in
  let rec check_defs (ds:(string * string list) list):unit =
    // move definitions with no unresolved dependencies to front
    let (defs_ready, defs_wait) = List.partition (fun (x, deps) -> List.isEmpty deps) ds in
    match (defs_ready @ defs_wait) with
    | [] -> ()
    | (d,[])::_ when not (List.mem d decls) -> err (d ^ " not declared in current module")
    | (d,[])::ds when (List.mem_assoc d ds) -> err (d ^ " defined more than once")
    | (d,[])::ds -> check_defs (List.map (fun (d2,deps) -> (d2, list_remove d deps)) ds)
    | (d1,(d2::_))::_ -> err (d1 ^ " and " ^ d2 ^ " circularly defined")
  in
  let () = check_defs ((List.map (fun d -> (d, [])) undefs) @ defs) in
  pub_decls @ scopeVars

let s_cmp (c:cmp): string =
  match c with
  | Eq -> "je"
  | Ne -> "jne"
  | Le -> "jbe"
  | Lt -> "jb"
  | Ge -> "jae"
  | Gt -> "ja"

let sw_reg (w:width) (r:reg): string =
  match (w, r) with
  | (W32, Eax) -> "eax"
  | (W32, Ebx) -> "ebx"
  | (W32, Ecx) -> "ecx"
  | (W32, Edx) -> "edx"
  | (W32, Esi) -> "esi"
  | (W32, Edi) -> "edi"
  | (W32, Ebp) -> "ebp"
  | (W32, Esp) -> "esp"
  | (W16, Eax) -> "ax"
  | (W16, Ebx) -> "bx"
  | (W16, Ecx) -> "cx"
  | (W16, Edx) -> "dx"
  | (W8, Eax) -> "al"
  | (W8, Ebx) -> "bl"
  | (W8, Ecx) -> "cl"
  | (W8, Edx) -> "dl"
  | _ -> err "unexpected register"
let s_reg (r:reg): string = sw_reg W32 r

let var_operand (ctxt:string) ((is_global:bool), (x:string)): string =
  "dword ptr " ^ (if is_global then global_var_name x else local_var_name ctxt x)

let simple_w_operand (w:width) (o:operand): string =
  match (w, o) with
  | (W32, OConst i) -> i
  | (_, OReg r) -> sw_reg w r
  | _ -> err "unexpected operand"
let simple_operand (o:operand): string = simple_w_operand W32 o

let src_operand (ctxt:string) (o:operand): string =
  match o with
  | OConst i -> i
  | OReg r -> s_reg r
  | OVar x -> var_operand ctxt x
  | _ -> err "unexpected operand"

let rm_operand (ctxt:string) (o:operand): string =
  match o with
  | OReg r -> s_reg r
  | OVar x -> var_operand ctxt x
  | _ -> err "unexpected operand"

let addr_operand (o:operand): string =
  match o with
  (* TODO: check offset and scale *)
  (* TODO: 1-byte and 2-byte mems *)
  | OReg r -> s_reg r
  | OOffset (r, i) -> (s_reg r) ^ " + " ^ (i)
  | OIndex (rb, s, rs, i) -> (s_reg rb) ^ " + " ^ (s) ^ " * " ^ (s_reg rs) ^ " + " ^ (i)
  | _ -> err "unexpected operand"

let mem_operand (width:width) (o:operand): string = (string_of_width width) ^ " ptr [" ^ (addr_operand o) ^ "]"

let s_pair (s1:string) (s2:string): string = s1 ^ ", " ^ s2

let bin_operands (ctxt:string) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([OReg rd], [OReg r1; o2]) when rd = r1 -> s_pair (s_reg rd) (src_operand ctxt o2)
  | ([OVar xd], [OVar x1; o2]) when xd = x1 -> s_pair (var_operand ctxt xd) (simple_operand o2)
  | _ -> err "unexpected operands"

let shift_operands (ctxt:string) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([OReg rd], [OReg r1; OConst i]) when rd = r1 -> s_pair (s_reg rd) i
  | ([OReg rd], [OReg r1; OReg Ecx]) when rd = r1 -> s_pair (s_reg rd) "cl"
  | ([OVar xd], [OVar x1; OConst i]) when xd = x1 -> s_pair (var_operand ctxt xd) i
  | ([OVar xd], [OVar x1; OReg Ecx]) when xd = x1 -> s_pair (var_operand ctxt xd) "cl"
  | _ -> err "unexpected operands"

let mul_operands (ctxt:string) (dsts:operand list) (srcs:operand list): string =
  (* TODO: operand o2 cannot be a constant *)
  match (dsts, srcs) with
  | ([OReg Eax; OReg Edx], [OReg Eax; o2]) -> (src_operand ctxt o2)
  | _ -> err "unexpected operands"

let div_operands (ctxt:string) (dsts:operand list) (srcs:operand list): string =
  (* TODO: operand o2 cannot be a constant *)
  match (dsts, srcs) with
  | ([OReg Eax; OReg Edx], [OReg Eax; OReg Edx; o2]) -> (rm_operand ctxt o2)
  | _ -> err "unexpected operands"

let unary_operands1 (ctxt:string) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([OReg rd], [OReg rs]) when rd = rs -> (s_reg rd)
  | ([OVar xd], [OVar xs]) when xd = xs -> (var_operand ctxt xd)
  | _ -> err "unexpected operands"

let unary_operands2 (ctxt:string) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([OReg rd], [o2]) -> s_pair (s_reg rd) (src_operand ctxt o2)
  | ([OVar xd], [o2]) -> s_pair (var_operand ctxt xd) (simple_operand o2)
  | _ -> err "unexpected operands"

let lea_operands (ctxt:string) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([OReg rd], [o2]) -> s_pair (s_reg rd) (mem_operand W32 o2)
  | _ -> err "unexpected operands"

let lea_signed_index_operands (ctxt:string) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([OReg rd], [OReg r1; OConst c1; OReg r2; OConst c2]) -> s_pair (s_reg rd) ("dword ptr [" ^ (s_reg r1) ^ " + " ^ c1 ^ " * " ^ (s_reg r2) ^ " + " ^ c2 ^ "]")
  | _ -> err "unexpected operands"

let load_operands (ctxt:string) (width:width) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([OReg rd], [o2]) -> s_pair (s_reg rd) (mem_operand width o2)
  | _ -> err "unexpected operands"

let iom_reg_load_operands (ctxt:string) (width:width) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([OReg rd], [_; o2]) -> s_pair (s_reg rd) (mem_operand width o2)
  | _ -> err "unexpected operands"

let store_operands (ctxt:string) (width:width) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([], [o1; o2]) -> s_pair (mem_operand width o1) (simple_w_operand width o2)
  | _ -> err "unexpected operands"

let idt_store_operands (ctxt:string) (width:width) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([], [_; _; _; o1; o2]) -> s_pair (mem_operand width o1) (simple_w_operand width o2)
  | _ -> err "unexpected operands"

let iom_reg_store_operands (ctxt:string) (width:width) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([], [_; o1; o2]) -> s_pair (mem_operand width o1) (simple_w_operand width o2)
  | _ -> err "unexpected operands"

let lidt_operands (ctxt:string) (dsts:operand list) (srcs:operand list): string =
  match (dsts, srcs) with
  | ([], [OReg rs]) -> "fword ptr [" ^ (s_reg rs) ^ "]"
  | _ -> err "unexpected operands"

let cmp_operands (ctxt:string) (src1:operand) (src2:operand): string =
  match (src1, src2) with
  (* TODO: o1 cannot be OConst *)
  (* TODO: support more cases ? *)
  | (OReg r1, o2) -> s_pair (s_reg r1) (src_operand ctxt o2)
  | (o1, OReg r2) -> s_pair (src_operand ctxt o1) (s_reg r2)
  | _ -> err "unexpected operands"

let print_ins (ctxt:string) (i:string) (dsts:operand list) (srcs:operand list): unit =
  let bin s = print_endline ("    " ^ s ^ " " ^ (bin_operands ctxt dsts srcs)) in
  let check_over () = print_endline "    jc _?Overflow" in
  match i with
  | "Mov" -> print_endline ("    mov " ^ (unary_operands2 ctxt dsts srcs))
  | "Not" -> print_endline ("    not " ^ (unary_operands1 ctxt dsts srcs))
  | "Add" -> bin "add"
  | "AddChecked" -> bin "add"; check_over ()
  | "Sub" -> bin "sub"
  | "SubChecked" -> bin "sub"; check_over ()
  | "Mul" -> print_endline ("    mul " ^ (mul_operands ctxt dsts srcs))
  | "MulChecked" -> print_endline ("    mul " ^ (mul_operands ctxt dsts srcs)); check_over ()
  | "Div" -> print_endline ("    div " ^ (div_operands ctxt dsts srcs))
  | "And" -> bin "and"
  | "Or" -> bin "or"
  | "Xor" -> bin "xor"
  | "Shl" -> print_endline ("    shl " ^ (shift_operands ctxt dsts srcs))
  | "Shr" -> print_endline ("    shr " ^ (shift_operands ctxt dsts srcs))
  | "KeyboardDataIn8" -> print_endline "    in al, 060h"
  | "KeyboardStatusIn8" -> print_endline "    in al, 064h"
  | "PicOut8" -> print_endline "    out dx, al"
  | "PitModeOut8" -> print_endline "    out 43h, al"
  | "PitFreqOut8" -> print_endline "    out 40h, al"
  | "PciConfigAddrOut32" -> print_endline "    out dx, eax"
  | "PciConfigDataOut32" -> print_endline "    out dx, eax"
  | "PciConfigDataIn32" -> print_endline "    in eax, dx"
  | "RoLoadU8" ->
      print_endline ("    movzx " ^ (load_operands ctxt W8 dsts srcs))
  | "RoLoadS8" ->
      print_endline ("    movsx " ^ (load_operands ctxt W8 dsts srcs))
  | "RoLoadU16" ->
      print_endline ("    movzx " ^ (load_operands ctxt W16 dsts srcs))
  | "RoLoadS16" ->
      print_endline ("    movsx " ^ (load_operands ctxt W16 dsts srcs))
  | "RoLoad32" | "Load" | "SectionLoad" ->
      print_endline ("    mov " ^ (load_operands ctxt W32 dsts srcs))
  | "IomRegLoad" | "PciMemLoad32" ->
      print_endline ("    mov " ^ (iom_reg_load_operands ctxt W32 dsts srcs))
  | "VgaTextStore16" | "VgaDebugStore16" ->
      print_endline ("    mov " ^ (store_operands ctxt W16 dsts srcs))
  | "IdtStore" ->
      print_endline ("    mov " ^ (idt_store_operands ctxt W32 dsts srcs))
  | "IomRegStore" | "PciMemStore32" ->
      print_endline ("    mov " ^ (iom_reg_store_operands ctxt W32 dsts srcs))
  | "Store" | "SectionStore" | "IomStore" ->
      print_endline ("    mov " ^ (store_operands ctxt W32 dsts srcs))
  | "Lidt" -> print_endline ("    lidt " ^ (lidt_operands ctxt dsts srcs))
  | "Lea" -> print_endline ("    lea " ^ (lea_operands ctxt dsts srcs))
  | "LeaUnchecked" -> print_endline ("    lea " ^ (lea_operands ctxt dsts srcs))
  | "LeaSignedIndex" -> print_endline ("    lea " ^ (lea_signed_index_operands ctxt dsts srcs))
  | "Rdtsc" -> print_endline ("    rdtsc")
  | _ -> err ("instruction " ^ i ^ " : unsupported instruction or operands")

let rec print_stmt (ctxt:string) (inlines:inlineMap) (s:stmt): unit =
  match s with
  | SNone -> ()
  | SLabel l -> print_endline ("  " ^ label ctxt l ^ ":")
  | SGoto l -> print_endline ("    jmp " ^ (label ctxt l))
  | SReturn -> print_endline "    ret"
  | SIReturn -> print_endline "    iretd"
  | SIf (c, o1, o2, l) ->
      print_endline ("    cmp " ^ (cmp_operands ctxt o1 o2));
      print_endline ("    " ^ s_cmp c ^ " " ^ (label ctxt l))
  | SInline p -> try List.assoc p inlines () with :? System.Collections.Generic.KeyNotFoundException as x -> err (p ^ " not found")
  | SCall p ->
      assrt (List.mem_assoc p inlines); (* disallow recursion *)
      print_endline ("    call " ^ (procname p))
  | SIns (i, dsts, srcs) -> print_ins ctxt i dsts srcs

let print_locals (ctxt:string) (locals:string list): unit =
  print_endline ".data";
  print_endline "align 4";
  List.iter (fun x -> print_endline ((local_var_name ctxt x) ^ " DD 0")) locals;
  print_endline ".code";
  ()

let boogie_ins_count = ref 0
let x86_ins_count = ref 0
let checked_count = ref 0
let unchecked_count = ref 0
let count_instruction (s:stmt): unit =
  let x86 () = incr boogie_ins_count; incr x86_ins_count in
  let pseudo () = incr boogie_ins_count; incr x86_ins_count; incr x86_ins_count in
  match s with
  | SNone -> ()
  | SLabel l -> ()
  | SGoto l -> x86 ()
  | SReturn -> x86 ()
  | SIReturn -> x86 ()
  | SIf (c, o1, o2, l) -> pseudo ()
  | SInline p -> ()
  | SCall p -> x86 ()
  | SIns ("AddChecked", _, _) -> pseudo (); incr checked_count
  | SIns ("SubChecked", _, _) -> pseudo (); incr checked_count
  | SIns ("MulChecked", _, _) -> pseudo (); incr checked_count
  | SIns ("Add", _, _) -> x86 (); incr unchecked_count
  | SIns ("Sub", _, _) -> x86 (); incr unchecked_count
  | SIns ("Mul", _, _) -> x86 (); incr unchecked_count
  | SIns (_, _, _) -> x86 ()

let print_decl (inlines:inlineMap) (d:decl): inlineMap =
  match d with
  | DFunDecl _ -> inlines
  | DFunDef (x, [], EConst i) when BigInt.Zero <= i && i < (BigInt.Parse "4294967296") ->
      print_endline (x ^ " EQU " ^ ((string)i));
      inlines
  | DFunDef _ -> inlines
  | DVar x ->
      print_endline ".data";
      print_endline "align 4";
      print_endline ((global_var_name x) ^ " DD 0");
      inlines
  | DInline (p, locals, b) ->
      List.iter count_instruction b;
      (p, fun () -> let ctxt = gensym () in print_locals ctxt locals; List.iter (print_stmt ctxt inlines) b)::inlines
  | DProc (p, locals, b) ->
      List.iter count_instruction b;
      print_locals p locals;
      print_endline "align 16";
      print_endline ((procname p) ^ " proc");
      List.iter (print_stmt p inlines) b;
      print_endline ((procname p) ^ " endp");
      (p, fun () -> err ("cannot inline " ^ p))::inlines

let rec print_decls (inlines:inlineMap) (p:decl list): unit =
  match p with
  | [] -> ()
  | d::ds -> print_decls (print_decl inlines d) ds

let rec print_program (inlines:inlineMap) (p:decl list): unit =
  print_endline ".686p";
  print_endline ".model flat";
  print_endline "include trusted.inc";
  print_decls inlines p;
  print_endline "end";
  print_endline (";; boogie instructions  (before inlining): " ^ (string_of_int (!boogie_ins_count)));
  print_endline (";;    x86 instructions  (before inlining): " ^ (string_of_int (!x86_ins_count)));
  print_endline (";; unchecked arithmetic (before inlining): " ^ (string_of_int (!unchecked_count)));
  print_endline (";;   checked arithmetic (before inlining): " ^ (string_of_int (!checked_count)));
  ()

(* Each command-line argument is the name of a module *)
(* Each module M must contain two files: M_i.bpl and M.bpl *)
let main (argv) =
  try
  (
    let args = List.tl (Microsoft.FSharp.Collections.Array.to_list argv) in
    let parse_file name =
      print_endline (";;parsing " ^ name);
      line := 1;
      Parse.start Lex.token (Lexing.from_channel (open_in name)) in
    let modules = List.map (fun x -> (parse_file (x ^ "_i.bpl"), parse_file (x ^ ".bpl"))) args in
    let _ = List.fold check_module [] modules in
    print_program [] (List.concat (List.map (fun (x,y) -> x@y) modules))
    ()
  )
  with
     | Err s -> (print_endline "error:"; print_endline s; exit 1)
     | ParseErr x -> (print_endline ("error near line " ^ (string_of_int !line)); print_endline x; exit 1)
     | :? System.ArgumentException as x -> (print_endline ("error near line " ^ (string_of_int !line)); print_endline (x.ToString ()); exit 1)
     | Failure x -> (print_endline ("error near line " ^ (string_of_int !line)); print_endline x; exit 1)
     | x -> (print_endline (x.ToString ()); exit 1)
;;

(* TODO: check that procedure implementations are correctly placed and not duplicated? *)
(* TODO: check that no procedures are recursive, even if they aren't used (e.g. readField) *)

let () = main (System.Environment.GetCommandLineArgs ())


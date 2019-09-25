// -------------------------------------------------------------------------------
//    Wrap nonlinear ops so equality still works when nonlinear reasoning is off  
// -------------------------------------------------------------------------------

// definition axiom for _module.__default.INTERNAL__mul (intra-module)
axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
       { _module.__default.INTERNAL__mul($Heap, x#0, y#1) }
       _module.__default.INTERNAL__mul($Heap, x#0, y#1) == x#0 * y#1);

// definition axiom for _module.__default.INTERNAL__mul for all literals (intra-module)
axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
       {:weight 10} { _module.__default.INTERNAL__mul($Heap, Lit(x#0), Lit(y#1)) } 
       _module.__default.INTERNAL__mul($Heap, Lit(x#0), Lit(y#1)) == Lit(x#0 * y#1));

// definition axiom for _module.__default.INTERNAL__mod (intra-module)
axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
       { _module.__default.INTERNAL__mod($Heap, x#0, y#1) }
       _module.__default.INTERNAL__mod($Heap, x#0, y#1) == x#0 mod y#1);

// definition axiom for _module.__default.INTERNAL__mod for all literals (intra-module)
axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
       {:weight 10} { _module.__default.INTERNAL__mod($Heap, Lit(x#0), Lit(y#1)) } 
       _module.__default.INTERNAL__mod($Heap, Lit(x#0), Lit(y#1)) == Lit(x#0 mod y#1));

// definition axiom for _module.__default.INTERNAL__div (intra-module)
axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
       { _module.__default.INTERNAL__div($Heap, x#0, y#1) }
       _module.__default.INTERNAL__div($Heap, x#0, y#1) == x#0 div y#1);

// definition axiom for _module.__default.INTERNAL__div for all literals (intra-module)
axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
       {:weight 10} { _module.__default.INTERNAL__div($Heap, Lit(x#0), Lit(y#1)) } 
       _module.__default.INTERNAL__div($Heap, Lit(x#0), Lit(y#1)) == Lit(x#0 div y#1));


//// definition axiom for _module.__default.INTERNAL__mul__boogie (intra-module)
//axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
//       { _module.__default.INTERNAL__mul__boogie($Heap, x#0, y#1) }
//       _module.__default.INTERNAL__mul__boogie($Heap, x#0, y#1) == x#0 * y#1);
//
//// definition axiom for _module.__default.INTERNAL__mul__boogie for all literals (intra-module)
//axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
//       {:weight 10} { _module.__default.INTERNAL__mul__boogie($Heap, Lit(x#0), Lit(y#1)) } 
//       _module.__default.INTERNAL__mul__boogie($Heap, Lit(x#0), Lit(y#1)) == Lit(x#0 * y#1));
//
//// definition axiom for _module.__default.INTERNAL__mod__boogie (intra-module)
//axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
//       { _module.__default.INTERNAL__mod__boogie($Heap, x#0, y#1) }
//       _module.__default.INTERNAL__mod__boogie($Heap, x#0, y#1) == x#0 mod y#1);
//
//// definition axiom for _module.__default.INTERNAL__mod__boogie for all literals (intra-module)
//axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
//       {:weight 10} { _module.__default.INTERNAL__mod__boogie($Heap, Lit(x#0), Lit(y#1)) } 
//       _module.__default.INTERNAL__mod__boogie($Heap, Lit(x#0), Lit(y#1)) == Lit(x#0 mod y#1));
//
//// definition axiom for _module.__default.INTERNAL_div_boogie (intra-module)
//axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
//       { _module.__default.INTERNAL__div__boogie($Heap, x#0, y#1) }
//       _module.__default.INTERNAL__div__boogie($Heap, x#0, y#1) == x#0 div y#1);
//
//// definition axiom for _module.__default.INTERNAL__div__boogie for all literals (intra-module)
//axiom (forall $Heap: HeapType, x#0: int, y#1: int :: 
//       {:weight 10} { _module.__default.INTERNAL__div__boogie($Heap, Lit(x#0), Lit(y#1)) } 
//       _module.__default.INTERNAL__div__boogie($Heap, Lit(x#0), Lit(y#1)) == Lit(x#0 div y#1));

// ---------------------------------------------------------------

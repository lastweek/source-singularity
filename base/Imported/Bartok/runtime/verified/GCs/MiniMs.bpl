//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

function{:expand false} T(i:int) returns (bool) { true }
const NO_ABS:int, memLo:int, memHi:int;
axiom 0 < memLo && memLo <= memHi;
function memAddr(i:int) returns (bool) { memLo <= i && i < memHi }

function Unalloc(i:int) returns(bool) { i == 0 }
function White(i:int) returns(bool) { i == 1 }
function Gray(i:int) returns(bool) { i == 2 }
function Black(i:int) returns(bool) { i == 3 }

var Mem:[int,int]int, Color:[int]int;
var $toAbs:[int]int, $AbsMem:[int,int]int;

function WellFormed($toAbs:[int]int) returns(bool) {
  (forall i1:int,i2:int::{T(i1),T(i2)} T(i1) && T(i2) ==> memAddr(i1)
     && memAddr(i2)
     && $toAbs[i1] != NO_ABS
     && $toAbs[i2] != NO_ABS
     && i1 != i2
   ==> $toAbs[i1] != $toAbs[i2])
}

function Pointer($toAbs:[int]int, ptr:int, $abs:int) returns (bool) {
    memAddr(ptr) && $abs != NO_ABS
 && $toAbs[ptr] == $abs
}

function ObjInv(i:int, $toAbs:[int]int, $AbsMem:[int,int]int, Mem:[int,int]int) returns (bool) {
  $toAbs[i] != NO_ABS ==>
      Pointer($toAbs, Mem[i,0], $AbsMem[$toAbs[i],0])
   && Pointer($toAbs, Mem[i,1], $AbsMem[$toAbs[i],1])
}

function GcInv(Color:[int]int, $toAbs:[int]int, $AbsMem:[int,int]int, Mem:[int,int]int) returns (bool) {
    WellFormed($toAbs)
 && (forall i:int::{T(i)} T(i) ==> memAddr(i) ==>
        ObjInv(i, $toAbs, $AbsMem, Mem)
     && 0 <= Color[i] && Color[i] < 4
     && (Black(Color[i]) ==> !White(Color[Mem[i,0]])
                         && !White(Color[Mem[i,1]]))
     && ($toAbs[i] == NO_ABS <==> Unalloc(Color[i])))
}

function MutatorInv(Color:[int]int, $toAbs:[int]int, $AbsMem:[int,int]int, Mem:[int,int]int) returns (bool) {
    WellFormed($toAbs)
 && (forall i:int::{T(i)} T(i) ==> memAddr(i) ==>
        ObjInv(i, $toAbs, $AbsMem, Mem)
     && 0 <= Color[i] && Color[i] < 2
     && ($toAbs[i] == NO_ABS <==> Unalloc(Color[i])))
}

procedure Mark(ptr:int)
  requires GcInv(Color, $toAbs, $AbsMem, Mem);
  requires memAddr(ptr) && T(ptr);
  requires $toAbs[ptr] != NO_ABS;
  modifies Color;
  ensures  GcInv(Color, $toAbs, $AbsMem, Mem);
  ensures  (forall i:int::{T(i)} T(i) ==> !Black(Color[i]) ==>
                  Color[i] == old(Color)[i]);
  ensures  !White(Color[ptr]);
{
  if (White(Color[ptr])) {
    Color[ptr] := 2; // make gray
    call Mark(Mem[ptr,0]);
    call Mark(Mem[ptr,1]);
    Color[ptr] := 3; // make black
  }
}

procedure Sweep()
  requires GcInv(Color, $toAbs, $AbsMem, Mem);
  requires (forall i:int::{T(i)} T(i) ==> memAddr(i) ==> !Gray(Color[i]));
  modifies Color, $toAbs;
  ensures  MutatorInv(Color, $toAbs, $AbsMem, Mem);
  ensures  (forall i:int::{T(i)} T(i) ==> memAddr(i) ==>
      (Black(old(Color)[i]) ==> $toAbs[i] != NO_ABS)
   && ($toAbs[i] != NO_ABS ==>
         $toAbs[i] == old($toAbs)[i]));
{
  var ptr:int;
  ptr := memLo;
  while (ptr < memHi)
    invariant T(ptr) && memLo <= ptr && ptr <= memHi;
    invariant WellFormed($toAbs);
    invariant (forall i:int::{T(i)} T(i) ==> memAddr(i) ==>
        0 <= Color[i] && Color[i] < 4
     && !Gray(Color[i])
     && (Black(old(Color)[i]) ==>
            $toAbs[i] != NO_ABS
         && ObjInv(i, $toAbs, $AbsMem, Mem)
         && (Mem[i,0] >= ptr ==>
                !White(Color[Mem[i,0]]))
         && (Mem[i,1] >= ptr ==>
                !White(Color[Mem[i,1]])))
     && ($toAbs[i] == NO_ABS <==> Unalloc(Color[i]))
     && ($toAbs[i] != NO_ABS ==>
           $toAbs[i] == old($toAbs)[i])
     && (ptr <= i ==> Color[i] == old(Color)[i])
     && (i < ptr ==> 0 <= Color[i] && Color[i] < 2)
     && (i < ptr && White(Color[i]) ==>
           Black(old(Color)[i])));
  {
    if (White(Color[ptr])) {
      Color[ptr] := 0; // deallocate
      $toAbs[ptr] := NO_ABS;
    }
    else if (Black(Color[ptr])) {
      Color[ptr] := 1; // make white
    }
    ptr := ptr + 1;
  }
}

procedure GarbageCollect(root:int)
  requires MutatorInv(Color, $toAbs, $AbsMem, Mem);
  requires root != 0 ==>
             Pointer($toAbs, root, $toAbs[root]);
  modifies Color, $toAbs;
  ensures  MutatorInv(Color, $toAbs, $AbsMem, Mem);
  ensures  root != 0 ==> $toAbs[root] == old($toAbs)[root];
  ensures  root != 0 ==>
             Pointer($toAbs, root, $toAbs[root]);
  ensures  (forall i:int::{T(i)} T(i) ==> memAddr(i) && $toAbs[i] != NO_ABS ==>
    $toAbs[i] == old($toAbs)[i]);
{
  assert T(root);
  if (root != 0) {
    call Mark(root);
  }
  call Sweep();
}

procedure Initialize()
  modifies $toAbs, Color;
  ensures  MutatorInv(Color, $toAbs, $AbsMem, Mem);
  ensures  WellFormed($toAbs);
{
  var ptr:int;
  ptr := memLo;
  while (ptr < memHi)
    invariant T(ptr) && memLo <= ptr && ptr <= memHi;
    invariant (forall i:int::{T(i)} T(i) ==> memLo <= i && i <ptr ==>
      $toAbs[i] == NO_ABS && Unalloc(Color[i]));
  {
    Color[ptr] := 0;
    $toAbs[ptr] := NO_ABS;
    ptr := ptr + 1;
  }
}

procedure ReadField(ptr:int, field:int) returns (val:int)
  requires MutatorInv(Color, $toAbs, $AbsMem, Mem);
  requires Pointer($toAbs, ptr, $toAbs[ptr]);
  requires field == 0 || field == 1;
  ensures  Pointer($toAbs, val,
                   $AbsMem[$toAbs[ptr],field]);
{
  assert T(ptr);
  val := Mem[ptr,field];
}

procedure WriteField(ptr:int, field:int, val:int)
  requires MutatorInv(Color, $toAbs, $AbsMem, Mem);
  requires Pointer($toAbs, ptr, $toAbs[ptr]);
  requires Pointer($toAbs, val, $toAbs[val]);
  requires field == 0 || field == 1;
  modifies $AbsMem, Mem;
  ensures  MutatorInv(Color, $toAbs, $AbsMem, Mem);
  ensures  $AbsMem ==
    old($AbsMem)[$toAbs[ptr],field := $toAbs[val]];
{
  assert T(ptr) && T(val);
  Mem[ptr,field] := val;
  $AbsMem[$toAbs[ptr],field] := $toAbs[val];
}

procedure Alloc(root:int, $abs:int) returns (newRoot:int,ptr:int)
  requires MutatorInv(Color, $toAbs, $AbsMem, Mem);
  requires root != 0 ==>
             Pointer($toAbs, root, $toAbs[root]);
  requires $abs != NO_ABS;
  requires (forall i:int::{T(i)} T(i) ==> memAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs,0] == $abs;
  requires $AbsMem[$abs,1] == $abs;
  modifies Color, $toAbs, Mem;
  ensures  MutatorInv(Color, $toAbs, $AbsMem, Mem);
  ensures  WellFormed($toAbs);
  ensures  root != 0 ==>
             Pointer($toAbs, newRoot, old($toAbs)[root]);
  ensures  Pointer($toAbs, ptr, $abs);
{
  while (true)
    invariant MutatorInv(Color, $toAbs, $AbsMem, Mem);
    invariant root != 0 ==> $toAbs[root] == old($toAbs)[root];
    invariant root != 0 ==>
      Pointer($toAbs, root, $toAbs[root]);
    invariant (forall i:int::{T(i)} T(i) ==> memAddr(i) ==> $toAbs[i] != $abs);
  {
    ptr := memLo;
    while (ptr < memHi)
      invariant T(ptr) && memLo <= ptr && ptr <= memHi;
    {
      if (Unalloc(Color[ptr])) {
        Color[ptr] := 1; // make white
        $toAbs[ptr] := $abs;
        Mem[ptr,0] := ptr;
        Mem[ptr,1] := ptr;
        newRoot := root;
        return;
      }
      ptr := ptr + 1;
    }
    call GarbageCollect(root);
  }
}

//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

function{:expand false} T(i:int) returns (bool) { true }
const NO_ABS:int, memLo:int, memMid:int, memHi:int;
const MAP_NO_ABS:[int]int;
axiom (forall i:int::{T(i)} T(i) ==> MAP_NO_ABS[i] == NO_ABS);
axiom 0 < memLo && memLo <= memMid && memMid <= memHi;
function memAddr(i:int) returns (bool) { memLo <= i && i < memHi }

var Mem:[int,int]int, FwdPtr:[int]int;
var $toAbs:[int]int, $AbsMem:[int,int]int;
var $r1:[int]int, $r2:[int]int;

// Fromspace ranges from Fi to Fl, where Fk..Fl is empty
//   Tospace ranges from Ti to Tl, where Tk..Tl is empty
var Fi:int;
var Fk:int;
var Fl:int;
var Ti:int;
var Tj:int;
var Tk:int;
var Tl:int;

function WellFormed($r:[int]int) returns(bool) {
  (forall i1:int,i2:int::{T(i1),T(i2)} T(i1) && T(i2) ==> memAddr(i1)
     && memAddr(i2)
     && $r[i1] != NO_ABS
     && $r[i2] != NO_ABS
     && i1 != i2
   ==> $r[i1] != $r[i2])
}

function Pointer($r:[int]int, ptr:int, $abs:int) returns (bool) {
    memAddr(ptr) && $abs != NO_ABS
 && $r[ptr] == $abs
}

function ObjInv(i:int, $rs:[int]int, $rt:[int]int, $toAbs:[int]int, $AbsMem:[int,int]int, Mem:[int,int]int) returns (bool) {
  $rs[i] != NO_ABS ==>
      Pointer($rt, Mem[i,0], $AbsMem[$toAbs[i],0])
   && Pointer($rt, Mem[i,1], $AbsMem[$toAbs[i],1])
}

function GcInv(FwdPtr:[int]int, Fi:int, Fk:int, Fl:int, Ti:int, Tj:int, Tk:int, Tl:int,
               $r1:[int]int, $r2:[int]int, $toAbs:[int]int, $AbsMem:[int,int]int, Mem:[int,int]int) returns (bool) {
    WellFormed($toAbs)
 && memLo <= Fi && Fi <= Fk && Fk <= Fl && Fl <= memHi
 && memLo <= Ti && Ti <= Tj && Tj <= Tk && Tk <= Tl && Tl <= memHi
 && (Fl <= Ti || Tl <= Fi)
 && (forall i:int::{T(i)} T(i) ==> memAddr(i) ==>
        ($r2[i] != NO_ABS ==> $toAbs[i] == $r2[i])
     && ($r1[i] != NO_ABS <==> Fi <= i && i < Fk)
     && ($r2[i] != NO_ABS <==> Ti <= i && i < Tk)
     && (Fi <= i && i < Fk ==>
            (FwdPtr[i] == 0 <==> $toAbs[i] != NO_ABS)
         && (FwdPtr[i] != 0 ==> Pointer($r2, FwdPtr[i], $r1[i]))
         && (FwdPtr[i] == 0 ==> $toAbs[i] == $r1[i] && ObjInv(i, $r1, $r1, $toAbs, $AbsMem, Mem)))
     && (Ti <= i && i < Tk ==> FwdPtr[i] == 0 && $toAbs[i] != NO_ABS && $toAbs[i] == $r2[i])
     && (Ti <= i && i < Tj ==> ObjInv(i, $r2, $r2, $toAbs, $AbsMem, Mem))
     && (Tj <= i && i < Tk ==> ObjInv(i, $r2, $r1, $toAbs, $AbsMem, Mem)))
}

function MutatorInv(FwdPtr:[int]int, Fi:int, Fk:int, Fl:int, Ti:int, Tj:int, Tk:int, Tl:int,
                    $toAbs:[int]int, $AbsMem:[int,int]int, Mem:[int,int]int) returns (bool) {
    WellFormed($toAbs)
 && memLo <= Fi && Fi <= Fk && Fk <= Fl && Fl <= memHi
 && memLo <= Ti && Ti == Tj && Tj == Tk && Tk <= Tl && Tl <= memHi
 && (Fl <= Ti || Tl <= Fi)
 && (forall i:int::{T(i)} T(i) ==> memAddr(i) ==>
        ObjInv(i, $toAbs, $toAbs, $toAbs, $AbsMem, Mem)
     && (Fi <= i && i < Fk ==> FwdPtr[i] == 0)
     && ($toAbs[i] != NO_ABS <==> Fi <= i && i < Fk))
}

// As a region evolves, it adds new mappings, but each mapping is
// permanent: RExtend ensures that new mappings do not overwrite old mappings.
function RExtend(rOld:[int]int, rNew:[int]int) returns (bool)
{
  (forall i:int::{rOld[i]}{rNew[i]} rOld[i] != NO_ABS ==> rOld[i] == rNew[i])
}

procedure forwardFromspacePtr(ptr:int, $freshAbs:int) returns(ret:int)
  requires GcInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $r1, $r2, $toAbs, $AbsMem, Mem);
  requires T(ptr) && Fi <= ptr && ptr < Fk;
  requires T($freshAbs) && $freshAbs != NO_ABS;
  requires (forall i:int::{T(i)} T(i) ==> memAddr(i) ==> $toAbs[i] != $freshAbs);
  modifies FwdPtr, $toAbs, $r2, Tk, Mem;
  ensures  GcInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $r1, $r2, $toAbs, $AbsMem, Mem);
  ensures  T(ret) && Pointer($r2, ret, $r1[ptr]);
  ensures  (forall i:int::{T(i)} T(i) ==> memAddr(i) ==> $toAbs[i] != $freshAbs);
  ensures  (forall i:int::{T(i)} T(i) ==> i != old(Tk) ==> Mem[i, 0] == old(Mem)[i, 0]);
  ensures  (forall i:int::{T(i)} T(i) ==> i != old(Tk) ==> Mem[i, 1] == old(Mem)[i, 1]);
  ensures  RExtend(old($r2), $r2);
{
  if (FwdPtr[ptr] != 0) {
    // object already copied
    ret := FwdPtr[ptr];
  }
  else {
    // copy object to to-space
    while (Tk >= Tl) {
      // out of memory
    }
    assert T(ptr) && T(Tk);
    ret := Tk;
    Mem[ret, 0] := Mem[ptr, 0];
    Mem[ret, 1] := Mem[ptr, 1];
    FwdPtr[ret] := 0;
    $toAbs[ret] := $r1[ptr];
    $r2[ret] := $r1[ptr];
    $toAbs[ptr] := NO_ABS;
    FwdPtr[ptr] := ret;
    Tk := Tk + 1;
  }
}

procedure GarbageCollect(root:int, $freshAbs:int) returns(newRoot:int)
  requires MutatorInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $toAbs, $AbsMem, Mem);
  requires root != 0 ==>
             Pointer($toAbs, root, $toAbs[root]);
  requires T($freshAbs) && $freshAbs != NO_ABS;
  requires (forall i:int::{T(i)} T(i) ==> memAddr(i) ==> $toAbs[i] != $freshAbs);
  modifies FwdPtr, $toAbs, $r1, $r2, Fi, Fk, Fl, Ti, Tj, Tk, Tl, Mem;
  ensures  MutatorInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $toAbs, $AbsMem, Mem);
  ensures  root != 0 ==>
             Pointer($toAbs, newRoot, old($toAbs)[root]);
  ensures  (forall i:int::{T(i)} T(i) ==> memAddr(i) ==> $toAbs[i] != $freshAbs);
{
  var fwd0:int, fwd1:int, temp:int;
  assert T(root);
  $r1 := $toAbs;
  $r2 := MAP_NO_ABS;
  if (root != 0) {
    call newRoot := forwardFromspacePtr(root, $freshAbs);
  }
  while (Tj < Tk)
    invariant T(Tj) && T(root) && T(newRoot);
    invariant GcInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $r1, $r2, $toAbs, $AbsMem, Mem);
    invariant root != 0 ==>
               Pointer($r2, newRoot, old($toAbs)[root]);
    invariant (forall i:int::{T(i)} T(i) ==> memAddr(i) ==> $toAbs[i] != $freshAbs);
  {
    assert T(Mem[Tj,0]) && T(Mem[Tj,1]);
    call fwd0 := forwardFromspacePtr(Mem[Tj,0], $freshAbs);
    call fwd1 := forwardFromspacePtr(Mem[Tj,1], $freshAbs);
    Mem[Tj,0] := fwd0;
    Mem[Tj,1] := fwd1;
    Tj := Tj + 1;
  }
  temp := Fi;
  Fi := Ti;
  Ti := temp;

  temp := Fl;
  Fl := Tl;
  Tl := temp;

  Fk := Tk;
  Tj := Ti;
  Tk := Ti;

  $toAbs := $r2;
}

procedure Initialize()
  modifies $toAbs, FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl;
  ensures  MutatorInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $toAbs, $AbsMem, Mem);
  ensures  WellFormed($toAbs);
{
  $toAbs := MAP_NO_ABS;
  Fi := memLo;
  Fk := memLo;
  Fl := memMid;
  Ti := memMid;
  Tj := memMid;
  Tk := memMid;
  Tl := memHi;
}

procedure ReadField(ptr:int, field:int) returns (val:int)
  requires MutatorInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $toAbs, $AbsMem, Mem);
  requires Pointer($toAbs, ptr, $toAbs[ptr]);
  requires field == 0 || field == 1;
  ensures  Pointer($toAbs, val,
                   $AbsMem[$toAbs[ptr],field]);
{
  assert T(ptr);
  val := Mem[ptr,field];
}

procedure WriteField(ptr:int, field:int, val:int)
  requires MutatorInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $toAbs, $AbsMem, Mem);
  requires Pointer($toAbs, ptr, $toAbs[ptr]);
  requires Pointer($toAbs, val, $toAbs[val]);
  requires field == 0 || field == 1;
  modifies $AbsMem, Mem;
  ensures  MutatorInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $toAbs, $AbsMem, Mem);
  ensures  $AbsMem ==
    old($AbsMem)[$toAbs[ptr],field := $toAbs[val]];
{
  assert T(ptr) && T(val);
  Mem[ptr,field] := val;
  $AbsMem[$toAbs[ptr],field] := $toAbs[val];
}

procedure Alloc(root:int, $abs:int) returns (newRoot:int,ptr:int)
  requires MutatorInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $toAbs, $AbsMem, Mem);
  requires root != 0 ==>
             Pointer($toAbs, root, $toAbs[root]);
  requires $abs != NO_ABS;
  requires (forall i:int::{T(i)} T(i) ==> memAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs,0] == $abs;
  requires $AbsMem[$abs,1] == $abs;
  modifies FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $toAbs, Mem, $r1, $r2;
  ensures  MutatorInv(FwdPtr, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $toAbs, $AbsMem, Mem);
  ensures  WellFormed($toAbs);
  ensures  root != 0 ==>
             Pointer($toAbs, newRoot, old($toAbs)[root]);
  ensures  Pointer($toAbs, ptr, $abs);
{
  newRoot := root;
  assert T(root);
  if (Fk >= Fl) {
    call newRoot := GarbageCollect(root, $abs);
  }
  while (Fk >= Fl) {
    // out of memory
  }
  assert T(newRoot) && T(Fk);
  ptr := Fk;
  $toAbs[ptr] := $abs;
  $r1[ptr] := $abs;
  Mem[ptr,0] := ptr;
  Mem[ptr,1] := ptr;
  FwdPtr[ptr] := 0;
  Fk := Fk + 1;
}

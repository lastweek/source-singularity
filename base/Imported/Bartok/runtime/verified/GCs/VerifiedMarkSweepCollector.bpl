//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// Verified mark-sweep garbage collector
//
// medium term goal: support more Bartok array-of-struct and vector-of-struct object layouts
// long term goal: support various other features: threads, pinning, stack markers, etc.

// Imports:
//   - Trusted.bpl
//   - VerifiedBitVectors.bpl
// Includes:
//   - VerifiedCommon.bpl


// \Spec#\bin\Boogie.exe /noinfer Trusted.bpl VerifiedBitVectors.bpl VerifiedCommon.bpl VerifiedMarkSweepCollector.bpl

/*****************************************************************************
******************************************************************************
**** VERIFIED
******************************************************************************
*****************************************************************************/

//////////////////////////////////////////////////////////////////////////////
// MARK-SWEEP COLLECTOR
//////////////////////////////////////////////////////////////////////////////

// gc memory structure:
// ?gcLo [mark stack] ColorBase [color bit map] HeapLo [heap] HeapHi ?gcHi

function Unallocated(i:int) returns(bool) { i == 0 }
function White(i:int) returns(bool) { i == 1 }
function Gray(i:int) returns(bool) { i == 2 }
function Black(i:int) returns(bool) { i == 3 }

var $freshAbs:int;
var $color:[int]int;
var StackTop:int;
var $fs:[int]int; // size of free block
var $fn:[int]int; // next free block
var CachePtr:int;
var CacheSize:int;
var ColorBase:int;
var HeapLo:int;
var HeapHi:int;
var ReserveMin:int; // wilderness marker

function ObjectSeq(i1:int, i2:int, r:[int]int, $fs:[int]int, $fn:[int]int) returns (bool)
{
    (forall i:int::{TV(i)} TV(i) ==> i1 <= i && i < i2 ==>
        (r[i] != NO_ABS ==>
            $fs[i] == 0
         && i + 4 * numFields(r[i]) <= i2
         && (forall ii:int::{TV(ii)} TV(ii) ==> i < ii && ii < i + 4 * numFields(r[i]) ==> r[ii] == NO_ABS && $fs[ii] == 0)
        )
     && ($fs[i] != 0 ==>
            r[i] == NO_ABS
         && i + 8 <= i + $fs[i] && i + $fs[i] <= i2
         && Aligned(i) && Aligned(i + $fs[i])
         && ($fn[i] != 0 ==> between(i + $fs[i], i2, $fn[i]) && $fs[$fn[i]] != 0)
         && (forall ii:int::{TV(ii)} TV(ii) ==> i < ii && ii < i + $fs[i] ==> r[ii] == NO_ABS && $fs[ii] == 0)
         && (forall ii:int::{TV(ii)} TV(ii) ==> i < ii && ii < $fn[i] && $fs[ii] != 0 ==> $fn[ii] == 0)
        )
    )
}

function Objects(i1:int, i2:int, r:[int]int, $fs:[int]int, $fn:[int]int) returns (bool)
{
  (forall i:int::{TV(i)} TV(i) ==> i1 <= i && i < i2 ==>
        (r[i] != NO_ABS ==>
            $fs[i] == 0
         && Aligned(i)
         && i + 4 * numFields(r[i]) <= i2
         && (forall ii:int::{TV(ii)} TV(ii) ==> i < ii && ii < i + 4 * numFields(r[i]) ==> r[ii] == NO_ABS && $fs[ii] == 0)
        )
     && ($fs[i] != 0 ==> Aligned(i))
    )
}

function Disconnected(i1:int, ptr:int, $fs:[int]int, $fn:[int]int) returns(bool)
{
  (forall i:int::{TV(i)} TV(i) ==> i1 <= i && i < ptr && $fs[i] != 0 ==> $fn[i] != ptr)
}

function FreeInvBase(i1:int, i2:int, $fs:[int]int, $fn:[int]int, data:[int]int, CachePtr:int, CacheSize:int) returns (bool)
{
    i2 >= i1 + 8
 && $fs[i1] == 8
 && (CacheSize != 0 ==> between(i1, i2, CachePtr) && $fs[CachePtr] == CacheSize && Disconnected(i1, CachePtr, $fs, $fn))
}

function FreeInvI(i:int, i1:int, i2:int, $fs:[int]int, $fn:[int]int, data:[int]int, CachePtr:int, CacheSize:int) returns (bool)
{
        data[i] == $fn[i]
     && data[i + 4] == $fs[i]
}

function FreeInv(i1:int, i2:int, $fs:[int]int, $fn:[int]int, data:[int]int, CachePtr:int, CacheSize:int) returns (bool)
{
    FreeInvBase(i1, i2, $fs, $fn, data, CachePtr, CacheSize)
 && (forall i:int::{TV(i)} TV(i) ==> i1 <= i && i < i2 && $fs[i] != 0 ==>
      FreeInvI(i, i1, i2, $fs, $fn, data, CachePtr, CacheSize))
}

// REVIEW: get rid of this?
function AllocInv2($toAbs:[int]int, min:int, max:int, $r1:[int]int, $r2:[int]int, r1Live:bool) returns (bool)
{
    (forall i:int::{TV(i)} TV(i) ==> min <= i && i < max && r1Live ==> ($toAbs[i] == NO_ABS ==> $r1[i] == NO_ABS))
 && (forall i:int::{TV(i)} TV(i) ==> min <= i && i < max ==> ($toAbs[i] == NO_ABS ==> $r2[i] == NO_ABS))
}

function MsInvColorI(i:int, t:Time, $r1:[int]int, $r2:[int]int, $color:[int]int, r1Live:bool,
  $GcMem:[int]int, $toAbs:[int]int, $AbsMem:[int][int]int, $gcSlice:[int]int) returns (bool)
{
     (White($color[i]) ==> $r1[i] != NO_ABS && $r2[i] == NO_ABS
       && (r1Live ==> ObjInv(i, $r1, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice))
     )
  && (Gray($color[i])  ==> $r1[i] != NO_ABS && $r2[i] != NO_ABS
       && ObjInv(i, $r1, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice)
       && reached($toAbs[i], t)
     )
  && (Black($color[i]) ==> $r1[i] != NO_ABS && $r2[i] != NO_ABS
       && ObjInv(i, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice)
       && reached($toAbs[i], t)
     )
}

function MsInvBase(min:int, max:int, $r1:[int]int, $r2:[int]int, $color:[int]int,
  r1Live:bool, $GcMem:[int]int, $toAbs:[int]int, $gcSlice:[int]int) returns (bool)
{
     (forall i:int::{TV(i)} TV(i) ==> min <= i && i < max
        && r1Live && $r1[i] != NO_ABS && $r2[i] != NO_ABS ==> $r1[i] == $r2[i])
  && (forall i:int::{TV(i)} TV(i) ==> min <= i && i < max && $toAbs[i] != NO_ABS ==>
       $toAbs[i] != NO_ABS && $toAbs[i] == $r1[i])
  && WellFormed($toAbs)
}

function MsGcInv(min:int, max:int, t:Time, $r1:[int]int, $r2:[int]int, $color:[int]int,
  r1Live:bool, $GcMem:[int]int, $toAbs:[int]int, $AbsMem:[int][int]int, $gcSlice:[int]int) returns (bool)
{
    MsInvBase(min, max, $r1, $r2, $color, r1Live, $GcMem, $toAbs, $gcSlice)
 && (forall i:int::{TV(i)} TV(i) ==> min <= i && i < max && $toAbs[i] != NO_ABS ==>
      MsInvColorI(i, t, $r1, $r2, $color, r1Live, $GcMem, $toAbs, $AbsMem, $gcSlice)
    )
}

function MsInv(min:int, max:int, $color:[int]int,
  $GcMem:[int]int, $toAbs:[int]int, $AbsMem:[int][int]int, $gcSlice:[int]int) returns (bool)
{
    (forall i:int::{TV(i)} TV(i) ==> min <= i && i < max ==> $toAbs[i] != NO_ABS ==>
        $toAbs[i] != NO_ABS
     && ObjInv(i, $toAbs, $toAbs, $toAbs, $AbsMem, $GcMem, $gcSlice)
    )
 && (forall i:int::{TV(i)} TV(i) ==> min <= i && i < max ==> (White($color[i]) <==> $toAbs[i] != NO_ABS))
 && WellFormed($toAbs)
}

function GcInv(ColorBase:int, HeapLo:int, HeapHi:int, $color:[int]int, $toAbs:[int]int, $r1:[int]int, $r2:[int]int, $GcMem:[int]int) returns(bool)
{
    ?gcLo <= ColorBase && ColorBase <= HeapLo && HeapLo <= HeapHi && HeapHi <= ?gcHi
 && Aligned(ColorBase) && Aligned(HeapLo) && Aligned(HeapHi)
 && bb2vec4($color, HeapLo, $GcMem, HeapLo, HeapLo, HeapHi, ColorBase, HeapLo)
 && (forall i:int::{TV(i)} TV(i) ==> i < HeapLo || i >= HeapHi ==>
      $toAbs[i] == NO_ABS && $r1[i] == NO_ABS && $r2[i] == NO_ABS)
 && (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> between(0, 4, $color[i]))
 && (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> (Unallocated($color[i]) <==> $toAbs[i] == NO_ABS))
}

function BigGcInv($freshAbs:int, ColorBase:int, HeapLo:int, HeapHi:int, $color:[int]int, $fs:[int]int, $fn:[int]int,
    $toAbs:[int]int, $r1:[int]int, $r2:[int]int, $AbsMem:[int][int]int, $GcMem:[int]int, $gcSlice:[int]int,
    CachePtr:int, CacheSize:int, $Time:Time) returns(bool)
{
    AllocInv2($toAbs, HeapLo, HeapHi, $r1, $r2, true)
 && MsGcInv(HeapLo, HeapHi, $Time, $r1, $r2, $color, true, $GcMem, $toAbs, $AbsMem, $gcSlice)
 && GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $r1, $r2, $GcMem)
 && ObjectSeq(HeapLo, HeapHi, $toAbs, $fs, $fn)
 && FreeInv(HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize)
 && (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $freshAbs && $r2[i] != $freshAbs)
}

function MutatorInv(ColorBase:int, HeapLo:int, HeapHi:int, $color:[int]int, $fs:[int]int, $fn:[int]int,
    $toAbs:[int]int, $AbsMem:[int][int]int, $GcMem:[int]int, $gcSlice:[int]int,
    CachePtr:int, CacheSize:int) returns(bool)
{
    MsInv(HeapLo, HeapHi, $color, $GcMem, $toAbs, $AbsMem, $gcSlice)
 && GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $toAbs, $toAbs, $GcMem)
 && ObjectSeq(HeapLo, HeapHi, $toAbs, $fs, $fn)
 && FreeInv(HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize)
}

function MarkStack(s1:int, s2:int, $toAbs:[int]int, $color:[int]int, stack:[int]int, extra:int) returns(bool)
{
    s1 <= s2
 && Aligned(s2)
 && (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != NO_ABS && Gray($color[i]) && i != extra ==>
      (exists s:int::{TV(s)} TV(s) && s1 <= s && s < s2 && Aligned(s) && stack[s] == i))
 && (forall s:int::{TV(s)} TV(s) ==> s1 <= s && s < s2 && Aligned(s) ==>
      gcAddr(stack[s]) && $toAbs[stack[s]] != NO_ABS && Gray($color[stack[s]]) && stack[s] != extra)
 && (forall s:int,t:int::{TV(s),TV(t)} TV(s) && TV(t) ==>
      s1 <= s && s < s2 ==> s1 <= t && t < s2 && Aligned(s) && Aligned(t) ==>
        s != t ==> stack[s] != stack[t])
}

procedure BB4Zero2($a:[int]int, $aBase:int, $i0:int, $i1:int, $i2:int, $k:int, $g1:int, $g2:int, $_i0:int, $_g1:int)
  requires eax == $g1;
  requires ebx == $g2;
  requires (forall i:int::{TV(i)} TV(i) && $i1 <= i && i < $i2 ==> $a[$aBase + (i - $i0)] == 0);
  requires Aligned($g1) && Aligned($g2);
  requires $i2 - $i1 == 16 * ($g2 - $g1);
  requires word($i1 - $i0) && word($i2 - $i0);
  requires ?gcLo <= $g1 && $g1 <= $g2 && $g2 <= ?gcHi;
  requires $i1 == $i0;
  modifies $GcMem;
  modifies eax, ebx, esi, edi, ebp, esp;
  ensures  bb2vec4($a, $aBase, $GcMem, $i0, $i1, $i2, $g1, $g2);
  ensures  (forall i:int::{TV(i)} TV(i) && !between($g1, $g2, i) ==> $GcMem[i] == old($GcMem)[i]);
{
  var $iter:int;
  esi := eax;
  $iter := $i1;
  //while (esi < $g2)
  loop:
    assert Aligned(esi) && TV(esi);
    assert $g1 <= esi && esi <= $g2;
    assert $iter - $i1 == 16 * (esi - $g1);
    assert bb2vec4($a, $aBase, $GcMem, $i0, $i1, $iter, $g1, $g2);
    assert (forall i:int::{TV(i)} TV(i) && !between($g1, $g2, i) ==> $GcMem[i] == old($GcMem)[i]);
    if (esi >= ebx) { goto loopEnd; }

    call __notAligned(esi);
    call __bb4Zero2($a, $aBase, $GcMem, $i0, $i1, $iter, $g1, $g2, esi);
    call GcStore(esi, 0);
    $iter := $iter + 64;
    call esi := Add(esi, 4);
    assert TO(1);
    goto loop;
  loopEnd:

  assert esi == $g2;
  assert $iter == $i2;
  esp := esp + 4; return;
}

procedure bb4GetColor($a:[int]int, $aBase:int, $i0:int, $i1:int, $i2:int, $k:int, $g1:int, $g2:int)
  requires bb2vec4($a, $aBase, $GcMem, $i0, $i1, $i2, $g1, $g2);
  requires word($k - $i0) && $i1 <= $k && $k < $i2;
  requires word($k) && word($i0) && Aligned($k) && Aligned($i0);
  requires word($i2 - $i0);
  requires eax == $g1;
  requires ebx == $k - $i0;
  requires Aligned($g1) && ?gcLo <= $g1 && $g2 <= ?gcHi;
  requires word($i1 - $i0) && word($i2 - $i0);
  modifies ebx, ecx, edx;
  ensures  ebx == $a[$aBase + ($k - $i0)];
{
  var $idx:int;
  var $bbb:int;
  $idx := $g1 + 4 * shr($k - $i0, 6);
  $bbb := and(shr($GcMem[$idx], and(shr($k - $i0, 1), 31)), 3);
  call __subAligned($k, $i0);
  call __bb4Get2Bit($a, $aBase, $GcMem, $i0, $i1, $i2, $k, $idx, $bbb, $g1, $g2);

  assert TV($g1);
  assert TO(shr(ebx, 6));

  ecx := ebx;
  call ecx := Shr(ecx, 6);
  call edx := Lea(eax + 4 * ecx);
  ecx := ebx;
  call ecx := Shr(ecx, 1);
  call ecx := And(ecx, 31);
  call edx := GcLoad(edx);
  ebx := edx;
  call ebx := Shr(ebx, ecx);
  call ebx := And(ebx, 3);
}

procedure bb4SetColor($a:[int]int, $val:int, $aBase:int, $i0:int, $i1:int, $i2:int, $k:int, $g1:int, $g2:int)
  requires bb2vec4($a, $aBase, $GcMem, $i0, $i1, $i2, $g1, $g2);
  requires word($k - $i0) && $i1 <= $k && $k < $i2;
  requires word($k) && word($i0) && Aligned($k) && Aligned($i0);
  requires word($i2 - $i0);
  requires 0 <= $val && $val <= 3;
  requires esi == $k - $i0;
  requires edi == $g1;
  requires edx == $val;
  requires Aligned($g1) && ?gcLo <= $g1 && $g2 <= ?gcHi;
  requires word($i1 - $i0) && word($i2 - $i0);
  modifies eax, esi, edi, ecx, edx, $GcMem;
  ensures  bb2vec4($a[$aBase + ($k - $i0) := $val], $aBase, $GcMem, $i0, $i1, $i2, $g1, $g2);
  ensures  $GcMem == old($GcMem)[$g1 + ColorIndex($i0, $k) := esi];
  ensures  Aligned($k - $i0);
{
  var $idx:int;
  var $bbb:int;
  var $_bbb:int;
  $idx := $g1 + 4 * shr($k - $i0, 6);
  $bbb := and($GcMem[$idx], neg(shl(3, and(shr($k - $i0, 1), 31))));
  $_bbb := or($bbb, shl($val, and(shr($k - $i0, 1), 31)));
  call __subAligned($k, $i0);
  call __bb4Set2Bit($a, $val, $aBase, $GcMem, $i0, $i1, $i2, $k, $idx, $bbb, $_bbb, $GcMem[$idx := $_bbb], $g1, $g2);
  assert TV($g1);
  assert TO(shr(esi, 6));

  ecx := esi;
  call esi := Shr(esi, 6);
  call edi := Lea(edi + 4 * esi);
  //assert edi == $idx;

  call ecx := Shr(ecx, 1);
  call ecx := And(ecx, 31);
  eax := 3;
  call eax := Shl(eax, ecx);
  call eax := Not(eax);
  call esi := GcLoad(edi);
  call esi := And(esi, eax);
  //assert $bbb == esi;

  call edx := Shl(edx, ecx);
  call esi := Or(esi, edx);
  assert $_bbb == esi;
  call GcStore(edi, esi);
}

procedure visit($_ptr:int, $abs:int, $extra:int)
  requires ecx == $_ptr;
  requires AllocInv2($toAbs, HeapLo, HeapHi, $r1, $r2, true);
  requires MsGcInv(HeapLo, HeapHi, $Time, $r1, $r2, $color, true, $GcMem, $toAbs, $AbsMem, $gcSlice);
  requires GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $r1, $r2, $GcMem);
  requires Value(true, $r1, $_ptr, $abs);
  requires !gcAddrEx($_ptr) || reached($toAbs[$_ptr - 4], $Time);
  requires TV($_ptr - 4);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $extra);
  requires $extra != 0 ==> Gray($color[$extra]);
  requires StackTop <= ColorBase;
  requires gcAddrEx($_ptr);

  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;

  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $extra);
  ensures  GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $r1, $r2, $GcMem);
  ensures  AllocInv2($toAbs, HeapLo, HeapHi, $r1, $r2, true);
  ensures  MsGcInv(HeapLo, HeapHi, $Time, $r1, $r2, $color, true, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
  ensures  Value(true, $r2, $_ptr, $abs);
  ensures  !gcAddrEx($_ptr) || !White($color[$_ptr - 4]);
  ensures  (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> Gray(old($color)[i]) ==> Gray($color[i]));
  ensures  (   (   old(StackTop < ColorBase) && $GcMem == old($GcMem)
                     [ColorBase + ColorIndex(HeapLo, $_ptr - 4) := $GcMem[ColorBase + ColorIndex(HeapLo, $_ptr - 4)]]
                     [old(StackTop) := $GcMem[old(StackTop)]])
                && between(ColorBase, HeapLo, ColorBase + ColorIndex(HeapLo, $_ptr - 4)))
            || $GcMem == old($GcMem);
{
  // call ebp := Lea(ecx - 4); REVIEW: add support for negative offsets to MASM generator
  ebp := ecx;
  call ebp := Sub(ebp, 4);

  ebx := ebp;
  call ebx := Sub(ebx, HeapLo);
  eax := ColorBase;
  call bb4GetColor($color, HeapLo, HeapLo, HeapLo, HeapHi, ebp, ColorBase, HeapLo);
  assert ebx == $color[ebp];

  if (ebx != 1) { goto end; } // !white
  eax := StackTop;
  if (eax != ColorBase) { goto skip1; }
    // stack overflow
    call DebugBreak();
  skip1:
  esi := ebp;
  call esi := Sub(esi, HeapLo);
  edi := ColorBase;
  edx := 2; // gray
  call bb4SetColor($color, 2, HeapLo, HeapLo, HeapLo, HeapHi, ebp, ColorBase, HeapLo);
  $color[ebp] := 2; // gray

  $r2[ebp] := $r1[ebp];
  eax := StackTop;
  call GcStore(eax, ebp);
  assert TV(StackTop) && TO(1);
  call __notAligned(StackTop);
  call StackTop := Add(StackTop, 4);
end:
}

procedure scanObjectDense($vt:int, $ptr:int, $abs:int)
  requires ebx == $ptr;
  requires ecx == $vt;
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires tag($vt) == ?DENSE_TAG;
  requires $abs == $r1[$ptr];
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;

  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;

  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));

{
  var ptr:int;
  var save1:int;
  var save2:int;
  var save3:int;
  assert TO(numFields($r1[$ptr]));
  ptr := ebx;

  esi := 2;
  assert TVT($r1[$ptr], $vt);
  assert TVL($r1[$ptr]);
  call ebp := RoLoad32(ecx + ?VT_BASE_LENGTH);
  call edx := RoLoad32(ecx + ?VT_MASK);
  edi := ebx;
  call edi := Add(edi, 8);
  call ebp := Add(ebp, ebx);

  //while (edi < ebp)
  loop:
    assert TO(esi);// && 0 < esi;
    assert edi == $ptr + 4 * esi && ebp == $ptr + 4 * numFields($r1[$ptr]) && edx == mask($vt);
    assert 2 <= esi && esi <= numFields($r1[$ptr]);
    assert Pointer($r2, $ptr, $r1[$ptr]);
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert old(StackTop) <= StackTop && StackTop <= ColorBase;
    assert (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
    assert Gray($color[$ptr]);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial($ptr, 0, esi, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial($ptr, esi, numFields($r1[$ptr]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[$ptr] != NO_ABS && $toAbs[$ptr] == $r1[$ptr];
    if (edi >= ebp) { goto loopEnd; }
    if (esi >= 30) { goto loopEnd; }

    assert TO(0) && TO(1);
    assert TVT($r1[$ptr], $vt);
    assert TVL($r1[$ptr]);
    call ecx := Lea(esi + 2);
    ebx := edx;
    call ebx := Shr(ebx, ecx);
    call ebx := And(ebx, 1);
    if (ebx != 1) { goto skip1; }
      call ecx := GcLoad(edi);

      //if (gcAddrEx(ecx))
      if (ecx < ?gcLo) { goto skip2; }
      if (ecx > ?gcHi) { goto skip2; }
        assert TV(ecx - 4);
        call reach($toAbs[$ptr], esi, $Time);

        save1 := esi;
        save2 := ebp;
        save3 := edx;
        call visit(ecx, $AbsMem[$toAbs[$ptr]][esi], $ptr);
        esi := save1;
        ebp := save2;
        edx := save3;
        edi := ptr;
        call edi := Lea(edi + 4 * esi);
      skip2:
    skip1:

    call esi := Add(esi, 1);
    call edi := Add(edi, 4);
    goto loop;
  loopEnd:

  assert TVT($r1[$ptr], $vt);
  assert TVL($r1[$ptr]);
  assert TO(1);
}

procedure scanObjectSparse($vt:int, $ptr:int, $abs:int)
  requires ebx == $ptr;
  requires ecx == $vt;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires tag($vt) == ?SPARSE_TAG;
  modifies $r2, $color, StackTop, $GcMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
{
  var save1:int;
  var save2:int;
  var save3:int;
  var save4:int;
  var ptr:int;
  ptr := ebx;
  assert TO(numFields($r1[$ptr]));

  esi := 1;

  assert TO(numFields($r1[$ptr]));
  assert TVT($r1[$ptr], $vt);
  call ebp := RoLoad32(ecx + ?VT_BASE_LENGTH);
  call edx := RoLoad32(ecx + ?VT_MASK);
  assert TVL($r1[$ptr]);

  esi := 1;
  //while (esi < 8)
  loop:
    assert edx == mask($vt) && ebp == 4 * numFields($r1[$ptr]);
    assert TSlot(esi) && 0 < esi && esi <= 8;
    assert Pointer($r2, $ptr, $r1[$ptr]);
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert old(StackTop) <= StackTop && StackTop <= ColorBase;
    assert (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
    assert Gray($color[$ptr]);
    assert RExtend(old($r2), $r2);
    assert ObjInvBase($ptr, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($r1[$ptr]) ==>
                between(1, esi, fieldToSlot($vt, j - 2)) ==>
                  ObjInvField($ptr, j, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($r1[$ptr]) ==>
                !between(1, esi, fieldToSlot($vt, j - 2)) ==>
                  ObjInvField($ptr, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert $toAbs[$ptr] != NO_ABS && $toAbs[$ptr] == $r1[$ptr];
    if (esi >= 8) { goto loopEnd; }

    assert TO(0) && TO(1);
    assert TVT($r1[$ptr], $vt);
    assert TO(getNib(edx, 4 * esi) + 1);

    //if (getNib(edx, 4 * esi) != 0)
    ecx := 0;
    call ecx := Lea(ecx + 4 * esi);
    ebx := edx;
    call ebx := Shr(ebx, ecx);
    call ebx := And(ebx, 15);
    if (ebx == 0) { goto skip1; }
      eax := ptr;
      call ecx := GcLoad(eax + 4 * ebx + 4);

      //if (gcAddrEx(ecx))
      if (ecx < ?gcLo) { goto skip2; }
      if (ecx > ?gcHi) { goto skip2; }
        assert TV(ecx - 4);
        call reach($toAbs[$ptr], 1 + ebx, $Time);

        save1 := esi;
        save2 := ebp;
        save3 := edx;
        save4 := ebx;
        call visit(ecx, $AbsMem[$toAbs[$ptr]][1 + getNib(edx, 4 * esi)], $ptr);
        esi := save1;
        ebp := save2;
        edx := save3;
        ebx := save4;
      skip2:
    skip1:

    call esi := Add(esi, 1);
    goto loop;
  loopEnd:

  assert TVT($r1[$ptr], $vt);
  assert TVL($r1[$ptr]);
  assert TO(1);
}

procedure scanObjectOtherVectorNoPointers($vt:int, $ptr:int, $abs:int)
  requires ebx == $ptr;
  requires ecx == $vt;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires tag($vt) == ?OTHER_VECTOR_TAG;
  requires arrayOf($vt) != ?TYPE_STRUCT || (arrayOf($vt) == ?TYPE_STRUCT && mask(arrayElementClass($vt)) == ?SPARSE_TAG);
  modifies $r2, $color, StackTop, $GcMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
{
  assert TO(numFields($r1[$ptr]));
  assert TVT($r1[$ptr], $vt);
}

procedure scanObjectOtherVectorPointersSparseFields($vt:int, $ptr:int, $abs:int, $jj:int, $index:int)
  requires edx == mask(arrayElementClass($vt));
  requires edi == $jj;
  requires ebp == $ptr;
  requires tag($vt) == ?OTHER_VECTOR_TAG;
  requires arrayOf($vt) == ?TYPE_STRUCT && tag(arrayElementClass($vt)) == ?SPARSE_TAG;
  requires TO($jj) && $jj == baseWords($vt) + Mult(arrayElementWords($vt), $index);
  requires $jj < numFields($abs);
  requires TO($index) && 0 <= $index; // && $index <= nElems;
  requires Mult(arrayElementWords($vt), $index) >= 0;
  requires reached($abs, $Time);
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires ObjInvPartial($ptr, 0, $jj, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires ObjInvPartial($ptr, $jj, numFields($r1[$ptr]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires $toAbs[$ptr] != NO_ABS && $toAbs[$ptr] == $r1[$ptr];
  requires (forall j:int::{TO(j)} TO(j) ==>
             between(0, arrayElementWords($vt), j - $jj) ==>
               ObjInvField($ptr, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));

  modifies $r2, $color, StackTop, $GcMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  Gray($color[$ptr]);
  ensures  RExtend(old($r2), $r2);
  ensures  ObjInvPartial($ptr, 0, $jj, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  ObjInvPartial($ptr, $jj + arrayElementWords($vt), numFields($r1[$ptr]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  $toAbs[$ptr] != NO_ABS && $toAbs[$ptr] == $r2[$ptr];
  ensures  (forall j:int::{TO(j)} TO(j) ==>
             between(0, arrayElementWords($vt), j - $jj) ==>
               between(1, 8, fieldToSlot(arrayElementClass($vt), j - $jj)) ==>
                 ObjInvField($ptr, j, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
  ensures  (forall j:int::{TO(j)} TO(j) ==>
             between(0, arrayElementWords($vt), j - $jj) ==>
               !between(1, 8, fieldToSlot(arrayElementClass($vt), j - $jj)) ==>
                 ObjInvField($ptr, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));
  ensures  edi == old(edi);
  ensures  edx == old(edx);
{
  var save1:int;
  var save2:int;
  var save3:int;
  var save4:int;
  var save5:int;

  assert TO(numFields($r2[$ptr]));
  assert TO(2);
  assert TVT($r2[$ptr], $vt);
  assert TVL($r2[$ptr]);

  esi := 1;
  //while (esi < 8)
  loop:
    assert TSlot(esi) && 0 < esi && esi <= 8;
    assert edx == mask(arrayElementClass($vt));
    assert edi == $jj;
    assert ebp == $ptr;

    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
               $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
    assert old(StackTop) <= StackTop && StackTop <= ColorBase;
    assert (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);

    assert Gray($color[$ptr]);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial($ptr, 0, $jj, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial($ptr, $jj + arrayElementWords($vt), numFields($r2[$ptr]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[$ptr] != NO_ABS && $toAbs[$ptr] == $r2[$ptr];
    assert (forall j:int::{TO(j)} TO(j) ==>
                between(0, arrayElementWords($vt), j - $jj) ==>
                  between(1, esi, fieldToSlot(arrayElementClass($vt), j - $jj)) ==>
                    ObjInvField($ptr, j, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert (forall j:int::{TO(j)} TO(j) ==>
                between(0, arrayElementWords($vt), j - $jj) ==>
                  !between(1, esi, fieldToSlot(arrayElementClass($vt), j - $jj)) ==>
                    ObjInvField($ptr, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));
    if (esi >= 8) { goto loopEnd; }

    // ebx := getNib(mask(arrayElementClass($vt)), 4 * esi);
    ecx := 0;
    call ecx := Lea(ecx + 4 * esi);
    ebx := edx;
    call ebx := Shr(ebx, ecx);
    call ebx := And(ebx, 15);
    assert ebx == getNib(mask(arrayElementClass($vt)), 4 * esi);

    // if (ebx != 0)
    if (ebx == 0) { goto skip1; }
      call ebx := Sub(ebx, 1);
      call ebx := Add(ebx, edi);
      assert TO(ebx);

      eax := ebp;
      call ecx := GcLoad(eax + 4 * ebx);
      //if (gcAddrEx(ecx))
      if (ecx < ?gcLo) { goto skip2; }
      if (ecx > ?gcHi) { goto skip2; }

        assert TV(ecx - 4);
        call reach($toAbs[$ptr], ebx, $Time);

        assert TO(0);
        assert TO(1);

        save1 := esi;
        save2 := edi;
        save3 := edx;
        save4 := ebx;
        save5 := ebp;
        call visit(ecx, $AbsMem[$toAbs[$ptr]][ebx], $ptr);
        esi := save1;
        edi := save2;
        edx := save3;
        ebx := save4;
        ebp := save5;

      skip2:
    skip1:
    call esi := Add(esi, 1);
    goto loop;
  loopEnd:
}

procedure scanObjectOtherVectorPointers($vt:int, $ptr:int, $abs:int)
  requires ebx == $ptr;
  requires ecx == $vt;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires tag($vt) == ?OTHER_VECTOR_TAG;
  requires arrayOf($vt) == ?TYPE_STRUCT && tag(arrayElementClass($vt)) == ?SPARSE_TAG;
  modifies $r2, $color, StackTop, $GcMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
{
  var save1:int;
  var save2:int;
  var ptr:int;

  var $index:int;

  assert TO(numFields($r2[$ptr]));
  assert TO(2);
  assert TVT($r2[$ptr], $vt);
  assert TVL($r2[$ptr]);

  $index := 0;

  ptr := ebx;
  edx := ebx;

  call edi := RoLoad32(ecx + ?VT_BASE_LENGTH);
  call ebx := RoLoad32(ecx + ?VT_ARRAY_ELEMENT_SIZE);
  call edx := GcLoad(edx + 8);
  eax := ebx;
  call eax, edx := MulChecked(eax, edx);
  call eax := AddChecked(eax, edi);
  call eax := AddChecked(eax, 3);
  edx := 3;
  call edx := Not(edx);
  call eax := And(eax, edx);
  ebp := eax;
  call edi := Shr(edi, 2);

  call ebx := Shr(ebx, 2); // arrayElementWords($vt)

  assert TVM(ebx, 0);
  call edx := RoLoad32(ecx + ?VT_ARRAY_ELEMENT_CLASS);
  call edx := RoLoad32(edx + ?VT_MASK);

  //while (4 * edi < ebp)
  loop:
    assert TO($index) && 0 <= $index;
    assert Mult(ebx, $index) >= 0;
    assert TO(edi) && edi == baseWords($vt) + Mult(ebx, $index);

    assert ebp == 4 * numFields($r2[$ptr]);
    assert edx == mask(arrayElementClass($vt));
    assert ebx == arrayElementWords($vt);
    assert 4 * edi <= ebp;

    assert Pointer($r2, $ptr, $r1[$ptr]);
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert old(StackTop) <= StackTop && StackTop <= ColorBase;
    assert (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
    assert Gray($color[$ptr]);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial($ptr, 0, edi, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial($ptr, edi, numFields($r2[$ptr]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[$ptr] != NO_ABS && $toAbs[$ptr] == $r2[$ptr];
    eax := 0;
    call eax := Lea(eax + 4 * edi);
    if (eax >= ebp) { goto loopEnd; }

    save1 := ebx;
    save2 := ebp;
    ebp := ptr;
    call scanObjectOtherVectorPointersSparseFields($vt, $ptr, $abs, edi, $index);
    ebx := save1;
    ebp := save2;

    assert TVM3(ebx, $index, 1);
    assert TVM(ebx, $index);
    $index := $index + 1;
    call edi := Add(edi, ebx);
    goto loop;
  loopEnd:

  assert TO(1);
}

procedure scanObjectPtrArray($vt:int, $ptr:int, $abs:int)
  requires ebx == $ptr;
  requires ecx == $vt;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires tag($vt) == ?PTR_ARRAY_TAG;
  modifies $r2, $color, StackTop, $GcMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
{
  var $ind:int;
  var save1:int;
  var save2:int;

  assert TO(numFields($r1[$ptr]));
  assert TO(3);
  assert TVT($r1[$ptr], $vt);
  assert TVL($r1[$ptr]);

  call ebp := GcLoad(ebx + 12);
  call esi := RoLoad32(ecx + ?VT_BASE_LENGTH);
  // size := pad(esi + 4 * ebp);
  call ebp := AddChecked(ebp, ebp);
  call ebp := AddChecked(ebp, ebp);
  call ebp := AddChecked(ebp, esi);
  call ebp := AddChecked(ebp, 3);
  eax := 3;
  call eax := Not(eax);
  call ebp := And(ebp, eax);
  call esi := Shr(esi, 2);
  $ind := esi;

  call edi := Lea(ebx + 4 * esi);
  call ebp := Add(ebp, ebx);

  //while (edi < ebp)
  loop:
    assert edi == $ptr + 4 * $ind;
    assert ebp == $ptr + 4 * numFields($r1[$ptr]);
    assert TO($ind) && baseWords($vt) <= $ind; // && $ind <= nElems + 3;
    assert Pointer($r2, $ptr, $r1[$ptr]);
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert old(StackTop) <= StackTop && StackTop <= ColorBase;
    assert (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
    assert Gray($color[$ptr]);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial($ptr, 0, $ind, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial($ptr, $ind, numFields($r1[$ptr]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[$ptr] != NO_ABS && $toAbs[$ptr] == $r1[$ptr];
    if (edi >= ebp) { goto loopEnd; }

    assert TO(0) && TO(1) && TO(3);
    assert TVT($r1[$ptr], $vt);
    assert TVL($r1[$ptr]);
    call ecx := GcLoad(edi);
    //if (gcAddrEx(ecx))
    if (ecx < ?gcLo) { goto skip1; }
    if (ecx > ?gcHi) { goto skip1; }
      assert TV(ecx - 4);
      call reach($toAbs[$ptr], $ind, $Time);

      save1 := edi;
      save2 := ebp;
      call visit(ecx, $AbsMem[$toAbs[$ptr]][$ind], $ptr);
      edi := save1;
      ebp := save2;
    skip1:

    $ind := $ind + 1;
    call edi := Add(edi, 4);
    goto loop;
  loopEnd:
}

procedure scanObjectPtrVector($vt:int, $ptr:int, $abs:int)
  requires ebx == $ptr;
  requires ecx == $vt;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires tag($vt) == ?PTR_VECTOR_TAG;
  modifies $r2, $color, StackTop, $GcMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
{
  var $ind:int;
  var save1:int;
  var save2:int;
  assert TO(numFields($r1[$ptr]));
  assert TO(2);
  assert TVT($r1[$ptr], $vt);
  assert TVL($r1[$ptr]);

  call ebp := GcLoad(ebx + 8);
  call esi := RoLoad32(ecx + ?VT_BASE_LENGTH);
  // size := pad(esi + 4 * ebp);
  call ebp := AddChecked(ebp, ebp);
  call ebp := AddChecked(ebp, ebp);
  call ebp := AddChecked(ebp, esi);
  call ebp := AddChecked(ebp, 3);
  eax := 3;
  call eax := Not(eax);
  call ebp := And(ebp, eax);
  call esi := Shr(esi, 2);
  $ind := esi;

  call edi := Lea(ebx + 4 * esi);
  call ebp := Add(ebp, ebx);

  //while (edi < ebp)
  loop:
    assert edi == $ptr + 4 * $ind;
    assert ebp == $ptr + 4 * numFields($r1[$ptr]);
    assert TO($ind) && baseWords($vt) <= $ind; // && $ind <= nElems + 3;
    assert Pointer($r2, $ptr, $r1[$ptr]);
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert old(StackTop) <= StackTop && StackTop <= ColorBase;
    assert (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
    assert Gray($color[$ptr]);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial($ptr, 0, $ind, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial($ptr, $ind, numFields($r1[$ptr]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[$ptr] != NO_ABS && $toAbs[$ptr] == $r1[$ptr];
    if (edi >= ebp) { goto loopEnd; }

    assert TO(0) && TO(1) && TO(2);
    assert TVT($r1[$ptr], $vt);
    call ecx := GcLoad(edi);
    //if (gcAddrEx(ecx))
    if (ecx < ?gcLo) { goto skip1; }
    if (ecx > ?gcHi) { goto skip1; }
      assert TV(ecx - 4);
      call reach($toAbs[$ptr], $ind, $Time);

      save1 := edi;
      save2 := ebp;
        call visit(ecx, $AbsMem[$toAbs[$ptr]][$ind], $ptr);
      edi := save1;
      ebp := save2;
    skip1:

    $ind := $ind + 1;
    call edi := Add(edi, 4);
    goto loop;
  loopEnd:
}

procedure scanObjectOtherArrayNoPointers($vt:int, $ptr:int, $abs:int)
  requires ebx == $ptr;
  requires ecx == $vt;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires tag($vt) == ?OTHER_ARRAY_TAG;
  requires arrayOf($vt) != ?TYPE_STRUCT;
  modifies $r2, $color, StackTop, $GcMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
{
  assert TO(numFields($r1[$ptr]));
  assert TVT($r1[$ptr], $vt);
}

procedure scanObjectString($vt:int, $ptr:int, $abs:int)
  requires ebx == $ptr;
  requires ecx == $vt;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires tag($vt) == ?STRING_TAG;
  modifies $r2, $color, StackTop, $GcMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
{
  assert TO(numFields($r1[$ptr]));
  assert TVT($r1[$ptr], $vt);
}

procedure scanObjectOther($vt:int, $ptr:int, $abs:int)
  requires ebx == $ptr;
  requires ecx == $vt;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires $vt == $AbsMem[$r1[$ptr]][1];
  requires isOtherTag(tag($vt));
  modifies $r2, $color, StackTop, $GcMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
{
  var save1:int;
  var save2:int;
  var save3:int;
  var save4:int;
  var save5:int;
  var ptr:int;
  ptr := ebx;

  assert TO(numFields($r1[$ptr]));
  assert TVT($r1[$ptr], $vt);
  assert TVL($r1[$ptr]);

  call edx := RoLoad32(ecx + ?VT_MASK);
  call edi := RoLoad32(edx);
  call ebp := RoLoad32(ecx + ?VT_BASE_LENGTH);

  esi := 1;

  //while (esi < edi + 1)
  loop:
    assert ebp == 4 * numFields($r1[$ptr]);
    assert edx == mask($vt);
    assert edi == ro32(mask($vt));
    assert TSlot(esi) && 0 < esi && esi <= ro32(mask($vt)) + 1;
    assert Pointer($r2, $ptr, $r1[$ptr]);
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert old(StackTop) <= StackTop && StackTop <= ColorBase;
    assert (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
    assert Gray($color[$ptr]);
    assert RExtend(old($r2), $r2);
    assert ObjInvBase($ptr, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($r1[$ptr]) ==>
                between(1, esi, fieldToSlot($vt, j)) ==>
                  ObjInvField($ptr, j, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($r1[$ptr]) ==>
                !between(1, esi, fieldToSlot($vt, j)) ==>
                  ObjInvField($ptr, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert $toAbs[$ptr] != NO_ABS && $toAbs[$ptr] == $r1[$ptr];
    if (esi > edi) { goto loopEnd; }

    assert TO(0) && TO(1);
    assert TVT($r1[$ptr], $vt);
    assert TVL($r1[$ptr]);
    assert TO(ro32(mask($vt) + 4 * esi) + 1);
    call ebx := RoLoad32(edx + 4 * esi);
    //if (ebx != 0)
    if (ebx == 0) { goto skip1; }
      eax := ptr;
      call ecx := GcLoad(eax + 4 * ebx + 4);

      //if (gcAddrEx(ecx))
      if (ecx < ?gcLo) { goto skip2; }
      if (ecx > ?gcHi) { goto skip2; }
        assert TV(ecx - 4);
        call reach($toAbs[$ptr], 1 + ro32(edx + 4 * esi), $Time);

        save1 := ebx;
        save2 := esi;
        save3 := edi;
        save4 := ebp;
        save5 := edx;
        call visit(ecx, $AbsMem[$toAbs[$ptr]][1 + ro32(edx + 4 * esi)], $ptr);
        ebx := save1;
        esi := save2;
        edi := save3;
        ebp := save4;
        edx := save5;
      skip2:
    skip1:
    call esi := AddChecked(esi, 1);
    goto loop;
  loopEnd:

  assert TVT($r1[$ptr], $vt);
  assert TVL($r1[$ptr]);
}

procedure scanObject($ptr:int, $abs:int)
  requires ebx == $ptr;
  requires $abs == $r1[$ptr];
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires Pointer($r1, $ptr, $abs);
  requires TV($ptr);
  requires Gray($color[$ptr]);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  requires StackTop <= ColorBase;

  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;

  ensures  old(StackTop) <= StackTop && StackTop <= ColorBase;
  ensures  (forall ss:int::{TV(ss)} TV(ss) ==> HeapHi <= ss && ss < old(StackTop) ==> $GcMem[ss] == old($GcMem)[ss]);
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, $ptr);
  ensures  RExtend(old($r2), $r2);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($abs) ==>
              Value(VFieldPtr($abs, j), $r2, $GcMem[$ptr + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
{
  var $vt:int;

  assert TO(1);
  call ecx := GcLoad(ebx + 4);
  $vt := ecx;

  assert TO(numFields($r1[$ptr]));

  call readTag($toAbs[$ptr], $vt);

  if (eax != ?SPARSE_TAG) { goto skip1; }
    call scanObjectSparse($vt, $ptr, $abs);
    goto end;
  skip1:

  if (eax != ?DENSE_TAG) { goto skip2; }
    call scanObjectDense($vt, $ptr, $abs);
    goto end;
  skip2:

  if (eax != ?STRING_TAG) { goto skip3; }
    call scanObjectString($vt, $ptr, $abs);
    goto end;
  skip3:

  if (eax != ?PTR_VECTOR_TAG) { goto skip4; }
    call scanObjectPtrVector($vt, $ptr, $abs);
    goto end;
  skip4:

  if (eax != ?OTHER_VECTOR_TAG) { goto skip5; }
    call readArrayOf($r1[$ptr], $vt);
    call readElementInfo($r1[$ptr], $vt);
    if (ebp != ?TYPE_STRUCT) { goto noPoint; }
    if (ebp != ?TYPE_STRUCT) { goto vecSkip1; }
    if (edi != ?SPARSE_TAG) { goto vecSkip1; }
    noPoint:
      call scanObjectOtherVectorNoPointers($vt, $ptr, $abs);
      goto end;
    vecSkip1:
    if (ebp != ?TYPE_STRUCT) { goto vecSkip2; }

    //if (tag(arrayElementClass(vt)) != ?SPARSE_TAG) { goto vecSkip2; }
    eax := edi;
    call eax := And(eax, 15);
    if (eax != ?SPARSE_TAG) { goto vecSkip2; }

      call scanObjectOtherVectorPointers($vt, $ptr, $abs);
      goto end;

    vecSkip2:
      assert !(
          (ebp != ?TYPE_STRUCT)
       || (ebp == ?TYPE_STRUCT && edi == ?SPARSE_TAG)
       || (ebp == ?TYPE_STRUCT && tag(arrayElementClass($vt)) == ?SPARSE_TAG));
      call DebugBreak();

  skip5:

  if (eax != ?PTR_ARRAY_TAG) { goto skip6; }
    call scanObjectPtrArray($vt, $ptr, $abs);
    goto end;
  skip6:

  if (eax != ?OTHER_ARRAY_TAG) { goto skip7; }
    call readArrayOf($r1[$ptr], $vt);
    if (ebp == ?TYPE_STRUCT) { goto arraySkip1; }
      call scanObjectOtherArrayNoPointers($vt, $ptr, $abs);
      goto end;
    arraySkip1:
      call DebugBreak();
    goto end;
  skip7:

    call scanObjectOther($vt, $ptr, $abs);
  end:
}

procedure FromInteriorPointer($iptr:int, $offset:int, $abs:int)
  requires ecx == $iptr;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires 0 <= $offset && $offset <= 4 * numFields($abs) - 4;
  requires Pointer($r1, $iptr - $offset - 4, $abs);
  modifies eax, ebx, ecx, edx, esp;
  ensures  eax == $offset;
{
  var save1:int;
  var save2:int;

  eax := 0;
//  while ($r1[$iptr - eax - 4] == NO_ABS)
  loop:
    assert $iptr - $offset <= $iptr - eax && $iptr - eax <= $iptr;
    assert TV($iptr - eax - 4) && TV($iptr - $offset - 4);
    assert ecx == $iptr;

    assert TV(?gcLo);
    assert TO($iptr - eax - 4 - HeapLo);

    ebx := ecx;
    call ebx := Sub(ebx, eax);
    call ebx := Sub(ebx, 4);
    call ebx := Sub(ebx, HeapLo);
    edx := ebx;
    call edx := And(edx, 3);
    call __andAligned(ebx);
    call __addAligned(HeapLo, ebx);
    if (edx != 0)
    {
      goto skip1;
    }

    save1 := eax;
    save2 := ecx;
    eax := ColorBase;
    call bb4GetColor($color, HeapLo, HeapLo, HeapLo, HeapHi, $iptr - save1 - 4, ColorBase, HeapLo);
    eax := save1;
    ecx := save2;

    if (ebx == 0) { goto skip1; }
      esp := esp + 4; return;
    skip1:
    call eax := Add(eax, 1);
  goto loop;
}

procedure scanStackUpdateInvs($r:[int]int, $f1:int, $f2:int, $frame:int, $addr:int, $v:int)
  requires $FrameSlice[$addr] == $frame;
  requires !($f1 <= $frame && $frame < $f2);
  requires (forall f:int::{TV(f)} TV(f) ==> $f1 <= f && f < $f2 ==>
    FrameInv(f, $FrameLayout[f], $r, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures  (forall f:int::{TV(f)} TV(f) ==> $f1 <= f && f < $f2 ==>
    FrameInv(f, $FrameLayout[f], $r, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem[$addr := $v], $FrameAbs, $FrameOffset, $Time));
{
  assert TO(0) && TO(1);
  assert (forall f:int::{TV(f)} TV(f) ==> TVF($FrameLayout[f]) && TVFT(f));
}

procedure scanStackWordDense($frame:int, $addr:int, $desc:int, $addrp:int, $p:int, $args:int)
  requires ecx == $addrp;
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  requires StackTop <= ColorBase;
  requires $desc == frameDescriptor($FrameLayout[$frame]);
  requires $addr == $FrameAddr[$frame];
  requires $FrameSlice[$addrp] == $frame;
  requires $args == frameLayoutArgs($FrameLayout[$frame]);
  requires $addrp == $addr + 4 * $p;
  requires getBit($desc, 0) && !getBit($desc, 1) && and(shr($desc, 6), 1023) == 0;
  requires frameHasPtr($FrameLayout[$frame], $p);
  requires 0 <= $frame && $frame < $FrameCount && TV($frame);
  requires (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f < $frame ==>
    FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  requires (forall f:int::{TV(f)} TV(f) ==> $frame < f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));

  requires $p <= 1 + $args && $p > $args - 1 - 16 && TO($p);
  requires (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f < $frame ==>
    FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  requires (forall f:int::{TV(f)} TV(f) ==> $frame < f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  requires FrameNextInv($frame, $FrameMem[$FrameAddr[$frame] + 4], $FrameMem[$FrameAddr[$frame]], $FrameAddr, $FrameLayout);
  requires (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && j <= $p ==>
      $FrameSlice[$addr + 4 * j] == $frame
   && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r1, $FrameMem[$addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[$addr + 4 * j])
   && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[$addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
   );
  requires (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && j > $p ==>
      $FrameSlice[$addr + 4 * j] == $frame
   && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r2, $FrameMem[$addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[$addr + 4 * j])
   && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[$addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
   );

  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;

  ensures  (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f < $frame ==>
    FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures  (forall f:int::{TV(f)} TV(f) ==> $frame < f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures  FrameNextInv($frame, $FrameMem[$FrameAddr[$frame] + 4], $FrameMem[$FrameAddr[$frame]], $FrameAddr, $FrameLayout);
  ensures  (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && j <= $p - 1 ==>
      $FrameSlice[$addr + 4 * j] == $frame
   && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r1, $FrameMem[$addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[$addr + 4 * j])
   && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[$addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
   );
  ensures  (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && j > $p - 1 ==>
      $FrameSlice[$addr + 4 * j] == $frame
   && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r2, $FrameMem[$addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[$addr + 4 * j])
   && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[$addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
   );
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  ensures  StackTop <= ColorBase;
  ensures  RExtend(old($r2), $r2);
{
  var save1:int;
  var v:int;
  var offset:int;
  assert TVF($FrameLayout[$frame]);
  assert TV($FrameMem[$addrp] - 4);

  call eax := FrameLoad(($frame), ecx);
  //if (gcAddrEx(eax))
  if (eax < ?gcLo) { goto skip1; }
  if (eax > ?gcHi) { goto skip1; }
    save1 := ecx;
    v := eax;

    ecx := eax;
    esp := esp - 4; call FromInteriorPointer(v, $FrameOffset[$addrp], $FrameAbs[$frame][$p]);
    offset := eax;

    ecx := v;
    call ecx := Sub(ecx, eax);
    assert TV(ecx - 4);

    call visit(ecx, $FrameAbs[$frame][$p], 0);

    assert TV(eax - 4);
    call scanStackUpdateInvs($r1, 0, $frame, $frame, $addrp, eax + offset);
    call scanStackUpdateInvs($r2, $frame + 1, $FrameCount, $frame, $addrp, eax + offset);

    ecx := save1;
  skip1:
}

procedure scanStackDense($frame:int, $addr:int, $desc:int)
  requires ecx == $addr;
  requires edx == $desc;
  requires $desc == frameDescriptor($FrameLayout[$frame]);
  requires $addr == $FrameAddr[$frame];
  requires getBit($desc, 0) && !getBit($desc, 1) && and(shr($desc, 6), 1023) == 0;
  requires 0 <= $frame && $frame < $FrameCount && TV($frame);
  requires (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f <= $frame ==>
    FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  requires (forall f:int::{TV(f)} TV(f) ==> $frame < f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  requires StackTop <= ColorBase;

  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;

  ensures (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f <= $frame - 1 ==>
    FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures (forall f:int::{TV(f)} TV(f) ==> $frame - 1 < f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  ensures  StackTop <= ColorBase;
  ensures  RExtend(old($r2), $r2);
{
  var b:int;
  var v:int;
  var offset:int;
  var args:int;
  var addr:int;
  var desc:int;
  var addrp:int;
  assert TVF($FrameLayout[$frame]);
  assert TO(0);

  addr := ecx;
  desc := edx;

  eax := edx;
  call eax := Shr(eax, 2);
  call eax := And(eax, 15);
  args := eax; // frameLayoutArgs($FrameLayout[$frame]);
  b := 0;
  ebx := 0;
  call ebx := Lea(ebx + 4 * eax + 4);
  call ebx := AddChecked(ebx, ecx);
  addrp := ebx;

  //while (b < args)
  loop1:
    assert addrp == $addr + 4 * (args + 1 - b);
    assert $frame < $FrameCount && TV($frame);
    assert 0 <= b && b <= args && TO(args + 1 - b);
    assert (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f < $frame ==>
      FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
    assert (forall f:int::{TV(f)} TV(f) ==> $frame < f && f < $FrameCount ==>
      FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));

    assert FrameNextInv($frame, $FrameMem[$FrameAddr[$frame] + 4], $FrameMem[$FrameAddr[$frame]], $FrameAddr, $FrameLayout);

    assert (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && j <= (args + 1 - b) ==>
        $FrameSlice[$addr + 4 * j] == $frame
     && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r1, $FrameMem[$addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[$addr + 4 * j])
     && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[$addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
     );

    assert (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && j > (args + 1 - b) ==>
        $FrameSlice[$addr + 4 * j] == $frame
     && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r2, $FrameMem[$addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[$addr + 4 * j])
     && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[$addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
     );

    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
               $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
    assert StackTop <= ColorBase;
    assert RExtend(old($r2), $r2);
    eax := b;
    if (eax >= args) { goto loopEnd1; }

    assert TVF($FrameLayout[$frame]);
    call ecx := Lea(eax + 16);
    ebx := desc;
    call ebx := Shr(ebx, ecx);
    call ebx := And(ebx, 1);
    //if (getBit($desc, 16 + b))
    if (ebx != 1) { goto skip1; }
      ecx := addrp;
      call scanStackWordDense($frame, $addr, $desc, $addr + 4 * (args + 1 - b), args + 1 - b, args);
    skip1:

    call b := Add(b, 1);
    call addrp := Sub(addrp, 4);
    goto loop1;
  loopEnd1:

  assert TO(0);
  assert TO(1);
  assert TV($FrameMem[$addr]);
  assert TV($FrameMem[$addr] - 4);

  call addrp := SubChecked(addrp, 8);

  //while (b < 16)
  loop2:
    assert addrp == $addr + 4 * (args - 1 - b);
    assert $frame < $FrameCount && TV($frame);
    assert (args - 1 - b) < 0 && (args - 1 - b) <= 1 + args && TO(args - 1 - b);
    assert (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f < $frame ==>
      FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
    assert (forall f:int::{TV(f)} TV(f) ==> $frame < f && f < $FrameCount ==>
      FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));

    assert FrameNextInv($frame, $FrameMem[$FrameAddr[$frame] + 4], $FrameMem[$FrameAddr[$frame]], $FrameAddr, $FrameLayout);

    assert (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && j <= (args - 1 - b) ==>
        $FrameSlice[$addr + 4 * j] == $frame
     && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r1, $FrameMem[$addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[$addr + 4 * j])
     && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[$addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
     );

    assert (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && j > (args - 1 - b) ==>
        $FrameSlice[$addr + 4 * j] == $frame
     && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r2, $FrameMem[$addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[$addr + 4 * j])
     && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[$addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
     );

    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
               $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
    assert StackTop <= ColorBase;
    assert RExtend(old($r2), $r2);
    eax := b;
    if (eax >= 16) { goto loopEnd2; }

    assert TVF($FrameLayout[$frame]);
    call ecx := Lea(eax + 16);
    ebx := desc;
    call ebx := Shr(ebx, ecx);
    call ebx := And(ebx, 1);
    //if (getBit($desc, 16 + b))
    if (ebx != 1) { goto skip2; }
      ecx := addrp;
      call scanStackWordDense($frame, $addr, $desc, $addr + 4 * (args - 1 - b), args - 1 - b, args);
    skip2:
    call b := Add(b, 1);
    call addrp := SubChecked(addrp, 4);
    goto loop2;
  loopEnd2:
}

procedure scanStackSparse8($frame:int, $addr:int, $desc:int)
  requires ecx == $addr;
  requires edx == $desc;
  requires $desc == frameDescriptor($FrameLayout[$frame]);
  requires $addr == $FrameAddr[$frame];
  requires !getBit($desc, 0) && ro32($desc) == 4096;
  requires 0 <= $frame && $frame < $FrameCount && TV($frame);
  requires (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f <= $frame ==>
    FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  requires (forall f:int::{TV(f)} TV(f) ==> $frame < f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
               $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  requires StackTop <= ColorBase;

  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;

  ensures (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f <= $frame - 1 ==>
    FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures (forall f:int::{TV(f)} TV(f) ==> $frame - 1 < f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
               $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  ensures  StackTop <= ColorBase;
  ensures  RExtend(old($r2), $r2);
{
  var p:int;
  var v:int;
  var addr:int;
  var desc:int;
  var addrp:int;
  var offset:int;
  var count:int;
  assert TVF($FrameLayout[$frame]);
  assert TO(0);

  addr := ecx;
  desc := edx;

  p := 0;
  call eax := RoLoadU8(edx + 4);
  count := eax;
  //while (p < count)
  loop:
    assert p >= 0 && TSlot(p);

    assert (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f < $frame ==>
      FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
    assert (forall f:int::{TV(f)} TV(f) ==> $frame < f && f < $FrameCount ==>
      FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));

    assert FrameNextInv($frame, $FrameMem[$FrameAddr[$frame] + 4], $FrameMem[$FrameAddr[$frame]], $FrameAddr, $FrameLayout);

    assert (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && !between(0, p, frameFieldToSlot($FrameLayout[$frame], j)) ==>
        $FrameSlice[addr + 4 * j] == $frame
     && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r1, $FrameMem[addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[addr + 4 * j])
     && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
     );

    assert (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) && between(0, p, frameFieldToSlot($FrameLayout[$frame], j)) ==>
        $FrameSlice[addr + 4 * j] == $frame
     && InteriorValue(frameHasPtr($FrameLayout[$frame], j), $r2, $FrameMem[addr + 4 * j], $FrameAbs[$frame][j], $FrameOffset[addr + 4 * j])
     && (frameHasPtr($FrameLayout[$frame], j) && gcAddrEx($FrameMem[addr + 4 * j]) ==> reached($FrameAbs[$frame][j], $Time))
     );

    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
               $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
    assert StackTop <= ColorBase;
    assert RExtend(old($r2), $r2);
    eax := p;
    if (eax >= count) { goto loopEnd; }

    assert TO(roS8(desc + 6 + p));
    assert TV($FrameMem[addr + 4 * roS8(desc + 6 + p)] - 4);
    ebx := desc;
    esi := addr;
    call ebp := RoLoadS8(ebx + 1 * eax + 6);
    call ebp := LeaSignedIndex(esi, 4, ebp, 0);
    addrp := ebp;
    call ecx := FrameLoad(($frame), ebp);
    //if (gcAddrEx(ecx))
    if (ecx < ?gcLo) { goto skip1; }
    if (ecx > ?gcHi) { goto skip1; }
      v := ecx;
      esp := esp - 4; call FromInteriorPointer(v, $FrameOffset[addr + 4 * roS8(desc + 6 + p)], $FrameAbs[$frame][roS8(desc + 6 + p)]);
      offset := eax;

      ecx := v;
      call ecx := Sub(ecx, eax);
      assert TV(ecx - 4);

        call visit(ecx, $FrameAbs[$frame][roS8(desc + 6 + p)], 0);
      assert TV(eax - 4);
      call scanStackUpdateInvs($r1, 0, $frame, $frame, addr + 4 * roS8(desc + 6 + p), eax);
      call scanStackUpdateInvs($r2, $frame + 1, $FrameCount, $frame, addr + 4 * roS8(desc + 6 + p), eax);
      ebx := addrp;
    skip1:

    // This is just here to improve performance:
    assert (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) &&
      p == frameFieldToSlot($FrameLayout[$frame], j) ==> j == roS8(desc + 6 + p));

    call p := Add(p, 1);
    goto loop;
  loopEnd:
}

procedure scanStack($ra:int, $nextFp:int)
  requires ecx == $ra && word($ra);
  requires edx == $nextFp;
  requires FrameNextInv($FrameCount, $ra, $nextFp, $FrameAddr, $FrameLayout);
  requires StackInv($r1, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  requires StackTop <= ColorBase;
  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;
  ensures  StackInv($r2, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  RExtend(old($r2), $r2);
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  ensures  StackTop <= ColorBase;
{
  var $frame:int;
  var p:int;
  var addr:int;
  var desc:int;
  var found:int;
  var _ra:int;
  var _nextFp:int;
  _ra := ecx;
  _nextFp := edx;

  $frame := $FrameCount - 1;
  loop:
    assert $frame < $FrameCount && TV($frame);
    assert word(_ra);
    assert FrameNextInv($frame + 1, _ra, _nextFp, $FrameAddr, $FrameLayout);
    assert (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f <= $frame ==>
      FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
    assert (forall f:int::{TV(f)} TV(f) ==> $frame < f && f < $FrameCount ==>
      FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
    assert StackTop <= ColorBase;
    assert RExtend(old($r2), $r2);

    assert TVF($FrameLayout[$frame]);

    ecx := _ra;
    edx := _nextFp;
    esp := esp - 4; call TablesSearch($frame + 1, _ra, _nextFp);
    desc := eax;
    found := edx;

    if (edx == 0) { goto loopEnd; }

    ecx := _nextFp;
    addr := ecx;
    assert TV(addr);
    assert TO(0);
    assert TO(1);
    call eax := FrameLoad(($frame), ecx);
    _nextFp := eax;
    call eax := FrameLoad(($frame), ecx + 4);
    _ra := eax;

    // if (getBit(desc, 0) && !getBit(desc, 1) && and(shr(desc, 6), 1023) == 0)
    eax := desc;
    call eax := Shr(eax, 0);
    call eax := And(eax, 1);
    if (eax != 1) { goto skip1; }
    eax := desc;
    call eax := Shr(eax, 1);
    call eax := And(eax, 1);
    if (eax == 1) { goto skip1; }
    eax := desc;
    call eax := Shr(eax, 6);
    call eax := And(eax, 1023);
    if (eax != 0) { goto skip1; }
      ecx := addr;
      edx := desc;
      call scanStackDense($frame, addr, desc);
      $frame := $frame - 1;
      goto loop;
    skip1:

    // else if (!getBit(desc, 0) && ro32(desc) == 4096)
    eax := desc;
    call eax := Shr(eax, 0);
    call eax := And(eax, 1);
    if (eax == 1) { goto skip2; }
    eax := desc;
    call eax := RoLoad32(eax);
    if (eax != 4096) { goto skip2; }
      ecx := addr;
      edx := desc;
      call scanStackSparse8($frame, addr, desc);
      $frame := $frame - 1;
      goto loop;
    skip2:

    // else
      assert !(   (getBit(desc, 0) && !getBit(desc, 1) && and(shr(desc, 6), 1023) == 0)
               || (!getBit(desc, 0) && ro32(desc) == 4096));
      call DebugBreak();

  loopEnd:
  assert $frame == 0 - 1;
}

procedure scanStaticSection($section:int)
  requires ecx == $section;
  requires 0 <= $section && $section < ?sectionCount && TV($section);
  requires (forall s:int::{TV(s)} TV(s) ==> $section <= s && s < ?sectionCount ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), $r1, $SectionMem, $SectionAbs, $Time));
  requires (forall s:int::{TV(s)} TV(s) ==> 0 <= s && s < $section ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), $r2, $SectionMem, $SectionAbs, $Time));
  ensures  (forall s:int::{TV(s)} TV(s) ==> $section + 1 <= s && s < ?sectionCount ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), $r1, $SectionMem, $SectionAbs, $Time));
  ensures  (forall s:int::{TV(s)} TV(s) ==> 0 <= s && s < $section + 1 ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), $r2, $SectionMem, $SectionAbs, $Time));

  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  requires StackTop <= ColorBase;

  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;

  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  StackTop <= ColorBase;
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  ensures  RExtend(old($r2), $r2);
{
  var sEnd:int;
  var addr:int;
  var section:int;
  var save1:int;
  var save2:int;
  var save3:int;

  section := ecx;

  assert TVS(section, 0);

  eax := ?dataSectionEnd;
  call eax := RoLoad32(eax + 4 * ecx);
  sEnd := eax;

  eax := ?staticDataPointerBitMap;
  call edx := RoLoad32(eax + 4 * ecx);

  eax := ?dataSectionBase;
  call eax := RoLoad32(eax + 4 * ecx);
  addr := eax;
  edi := eax;

  esi := 0;
  //while (edi < sEnd)
  loop:
    assert edx == ro32(?staticDataPointerBitMap + 4 * $section);
    assert edi == addr + 4 * esi;
    assert 0 <= section && TV(section);
    assert 0 <= esi && TO(esi);
    assert (forall s:int::{TV(s)} TV(s) ==> section < s && s < ?sectionCount ==>
      SectionInv(s, sectionBase(s), sectionEnd(s), $r1, $SectionMem, $SectionAbs, $Time));
    assert (forall s:int::{TV(s)} TV(s) ==> 0 <= s && s < section ==>
      SectionInv(s, sectionBase(s), sectionEnd(s), $r2, $SectionMem, $SectionAbs, $Time));

    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && addr + 4 * j < sectionEnd(section) && j >= esi ==>
        sectionSlice(addr + 4 * j) == section
     && Value(sectionHasPtr(section, j), $r1, $SectionMem[addr + 4 * j], $SectionAbs[section][j])
     && (sectionHasPtr(section, j) && gcAddrEx($SectionMem[addr + 4 * j]) ==> reached($SectionAbs[section][j], $Time))
    );

    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && addr + 4 * j < sectionEnd(section) && j < esi ==>
        sectionSlice(addr + 4 * j) == section
     && Value(sectionHasPtr(section, j), $r2, $SectionMem[addr + 4 * j], $SectionAbs[section][j])
     && (sectionHasPtr(section, j) && gcAddrEx($SectionMem[addr + 4 * j]) ==> reached($SectionAbs[section][j], $Time))
    );

    assert StackTop <= ColorBase;
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert RExtend(old($r2), $r2);

    if (edi >= sEnd) { goto loopEnd; }

    assert TVS(section, esi);
    eax := esi;
    call eax := Shr(eax, 5);
    call eax := RoLoad32(edx + 4 * eax);
    // assert getBit(v, and(esi, 31)) == sectionHasPtr(section, esi);
    //if (getBit(v, and(esi, 31)))
    ecx := esi;
    call ecx := And(ecx, 31);
    call eax := Shr(eax, ecx);
    call eax := And(eax, 1);
    if (eax != 1) { goto skip1; }
      assert TV($SectionMem[addr + 4 * esi] - 4);
      call ecx := SectionLoad(edi);
      //if (gcAddrEx(ecx))
      if (ecx < ?gcLo) { goto skip2; }
      if (ecx > ?gcHi) { goto skip2; }
        save1 := edi;
        save2 := esi;
        save3 := edx;
        call visit(ecx, $SectionAbs[section][esi], 0);
        edi := save1;
        esi := save2;
        edx := save3;
      skip2:
    skip1:

    call esi := Add(esi, 1);
    call edi := AddChecked(edi, 4);
    goto loop;
  loopEnd:
}

procedure scanStatic()
  requires StaticInv($r1, $SectionMem, $SectionAbs, $Time);
  ensures  StaticInv($r2, $SectionMem, $SectionAbs, $Time);

  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  requires StackTop <= ColorBase;

  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;

  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  StackTop <= ColorBase;
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  ensures  RExtend(old($r2), $r2);
{
  var section:int;
  section := 0;
  //while (section < ?sectionCount)
  loop:
    assert 0 <= section && TV(section);
    assert (forall s:int::{TV(s)} TV(s) ==> section <= s && s < ?sectionCount ==>
      SectionInv(s, sectionBase(s), sectionEnd(s), $r1, $SectionMem, $SectionAbs, $Time));
    assert (forall s:int::{TV(s)} TV(s) ==> 0 <= s && s < section ==>
      SectionInv(s, sectionBase(s), sectionEnd(s), $r2, $SectionMem, $SectionAbs, $Time));
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert StackTop <= ColorBase;
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
    assert RExtend(old($r2), $r2);
    ecx := section;
    if (ecx >= ?sectionCount) { goto loopEnd; }

    call scanStaticSection(section);
    call section := AddChecked(section, 1);
    goto loop;
  loopEnd:
}

procedure AllocBlock($minSize:int, $maxSize:int, $maxWords:int)
  requires ecx == $minSize;
  requires edx == $maxSize;
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires 8 <= $minSize && $minSize <= $maxSize;
  requires $maxSize == 4 * $maxWords;

  modifies $fs, $fn, $GcMem, CacheSize;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  eax != 0 ==> $fs[eax] >= $minSize;
  ensures  eax != 0 ==> HeapLo < eax && eax + $fs[eax] <= HeapHi;
  ensures  eax != 0 ==> Disconnected(HeapLo, eax, $fs, $fn);
  ensures  eax != 0 ==> CacheSize != 0 ==> eax != CachePtr;
  ensures  eax != 0 ==> Aligned(eax);
{
  edi := HeapLo;

  loop:
    assert MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
               $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
    assert HeapLo <= edi && edi < HeapHi;
    assert $fs[edi] != 0;

    assert TV(edi) && TV($fn[edi]) && TO(1);
    esi := edi;
    call edi := GcLoad(edi);
    if (edi != 0) { goto notEmpty; }
      eax := 0;
      esp := esp + 4; return;
    notEmpty:

    call ebx := GcLoad(edi + 4);
    //assert $fs[edi] == ebx;
    if (ebx < ecx) { goto loop; }
      ebp := ebx;
      call ebp := Sub(ebp, 8);
      if (ebp < edx) { goto skip1; }
        // Allocate from the end of the block
        assert TV(edi + $fs[edi]);
        assert TO(0 - $maxWords);
        call eax := Lea(edi + ebx);
        call eax := Sub(eax, edx);
        assert TV(eax);

        // If we dip below ReserveMin, skip this block
        if (eax < ReserveMin) { goto loop; }

        call ebx := Sub(ebx, edx);
        // If the remaining size is too small, allocate the whole block
        // TUNING: min cache size
        if (ebx < 256) { goto skip1; }
//        if (ebx < 1024) { goto skip1; }

        $fn[eax] := 0;
        $fs[eax] := edx;
        call GcStore(eax, 0);
        call GcStore(eax + 4, edx);

        $fs[edi] := $fs[edi] - edx;
        call GcStore(edi + 4, ebx);
        esp := esp + 4; return;
      skip1:
        // Allocate the whole block

        // If we dip below ReserveMin, skip this block
        if (edi < ReserveMin) { goto loop; }

        $fn[esi] := $fn[edi];
        call ebx := GcLoad(edi);
        call GcStore(esi, ebx);
        $fn[edi] := 0;
        call GcStore(edi, 0);
        eax := edi;
        esp := esp + 4; return;
}

procedure allocFromCache($size:int, $nFields:int)
  requires ecx == $size;
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires 8 <= $size && $size + 8 <= CacheSize;
  requires $size == 4 * $nFields;

  modifies $fs, $fn, $GcMem, CacheSize;
  modifies eax, edx;
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  $fs[eax] >= $size;
  ensures  HeapLo < eax && eax + $size <= HeapHi;
  ensures  Disconnected(HeapLo, eax, $fs, $fn);
  ensures  eax != CachePtr;
  ensures  Aligned(eax);
{
  assert TV(CachePtr) && TV(CachePtr + CacheSize);
  assert TO(0 - $nFields) && TO(1);
  call CacheSize := Sub(CacheSize, ecx);
  $fs[CachePtr] := CacheSize;
  eax := CacheSize;
  edx := CachePtr;
  call GcStore(edx + 4, eax);

  call eax := Add(eax, edx);
  assert TV(CachePtr) && TV(eax);

  $fn[eax] := 0;
  $fs[eax] := $size;
  call GcStore(eax, 0);
  call GcStore(eax + 4, ecx);
}

procedure AllocSlow($size:int, $nFields:int)
  requires ecx == $size;
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires 8 <= $size;
  requires $size == 4 * $nFields;
  modifies $fs, $fn, $GcMem, CachePtr, CacheSize;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  eax != 0 ==> $fs[eax] >= $size;
  ensures  eax != 0 ==> HeapLo < eax && eax + $size <= HeapHi;
  ensures  eax != 0 ==> Disconnected(HeapLo, eax, $fs, $fn);
  ensures  eax != 0 ==> CacheSize != 0 ==> eax != CachePtr;
  ensures  eax != 0 ==> Aligned(eax);
{
  var size:int;

  // TUNING: min cache size
  if (ecx < 192) { goto skip1; }
//  if (ecx < 768) { goto skip1; }
//  if (ecx < 1536) { goto skip1; }
    // Large object: allocate directly
    edx := ecx;
    esp := esp - 4; call AllocBlock($size, $size, $nFields);
    esp := esp + 4; return;
  //else
  skip1:
    // Small object: allocate from cache
    size := ecx;
  // TUNING: min cache size
    ecx := 256;
//    ecx := 1024;
//    ecx := 2048;
    edx := 65536;
  // TUNING: min cache size
    esp := esp - 4; call AllocBlock(256, 65536, 16384);
//    esp := esp - 4; call AllocBlock(1024, 65536, 16384);
//    esp := esp - 4; call AllocBlock(2048, 65536, 16384);
    assert TV(eax);
    if (eax == 0) { goto skip2; }
      CachePtr := eax;
      assert TO(1);
      ecx := CachePtr;
      call ecx := GcLoad(ecx + 4);
      CacheSize := ecx;
      ecx := size;
      call allocFromCache($size, $nFields);
    skip2:
    esp := esp + 4; return;
}

procedure processMarkStack()
  requires BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  requires MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  requires StackTop <= ColorBase;

  modifies $r2, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies StackTop, $GcMem;

  ensures  BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
  ensures  StackTop == ?gcLo;
  ensures  MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
  ensures  RExtend(old($r2), $r2);
{
  var ptr:int;
  eax := StackTop;

  // while (StackTop != ?gcLo)
  loop:
    assert MarkStack(?gcLo, StackTop, $toAbs, $color, $GcMem, 0);
    assert BigGcInv($freshAbs, ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs, $r1, $r2,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize, $Time);
    assert RExtend(old($r2), $r2);
    assert StackTop <= ColorBase;

    eax := StackTop;
    if (eax == ?gcLo) { goto loopEnd; }

    assert TV(StackTop) && TO(0 - 1);
    call __notAligned(?gcLo);
    call eax := Sub(eax, 4);
    call ebx := GcLoad(eax);
    ptr := ebx;
    StackTop := eax;
    assert TV(StackTop);
    assert TV(ptr);

    call __notAligned(StackTop);
    call scanObject(ptr, $r1[ptr]);

    esi := ptr;
    call esi := Sub(esi, HeapLo);
    edi := ColorBase;
    edx := 3; // black
    call bb4SetColor($color, 3, HeapLo, HeapLo, HeapLo, HeapHi, ptr, ColorBase, HeapLo);
    $color[ptr] := 3; // black
    goto loop;
  loopEnd:
}

procedure sweepObject($ptr:int, $prev:int, $regionStart:int) returns($_ptr:int, $_prev:int, $_regionStart:int)
  requires ebx == $color[$ptr];
  requires esi == $ptr;
  requires edi == $prev;
  requires ebp == $regionStart;
  requires $freshAbs != NO_ABS;
  requires HeapLo + 8 <= HeapHi;
  requires $toAbs[$ptr] != NO_ABS;
  requires Black($color[$ptr]) ==> $toAbs[$ptr] == $r2[$ptr];
  requires $ptr < HeapHi;

  requires GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $r1, $r2, $GcMem);
  requires ObjectSeq(HeapLo, $regionStart, $toAbs, $fs, $fn);
  requires FreeInv(HeapLo, $regionStart, $fs, $fn, $GcMem, CachePtr, CacheSize);
  requires Objects($ptr, HeapHi, $toAbs, $fs, $fn);
  requires $fs[$prev] != 0;
  requires $GcMem[$prev] == 0;
  requires Aligned($prev) && HeapLo <= $prev && $prev + 8 <= $regionStart && $regionStart <= $ptr;
  requires $ptr < HeapHi + 4;
  requires (forall ii:int::{TV(ii)} TV(ii) ==> HeapLo <= ii && ii < $prev && $fs[ii] != 0 ==> $fn[ii] <= $prev);
  requires (forall ii:int::{TV(ii)} TV(ii) ==> $prev <= ii && ii < $ptr && $fs[ii] != 0 ==> $fn[ii] == 0);
  requires (forall ii:int::{TV(ii)} TV(ii) ==> $regionStart <= ii && ii < $ptr ==> $toAbs[ii] == NO_ABS && $fs[ii] == 0);
  requires CacheSize == 0;
  requires HeapLo <= $ptr;
  requires Aligned($regionStart) && Aligned($ptr);
  requires AllocInv2($toAbs, HeapLo, HeapHi, $r1, $r2, false);
  requires (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> $toAbs[i] != NO_ABS ==> !Gray($color[i]));
  requires (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < $ptr ==> (White($color[i]) <==> $toAbs[i] != NO_ABS));
  requires (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < $ptr && $toAbs[i] != NO_ABS ==>
      $r1[i] != NO_ABS && $r2[i] != NO_ABS
   && $toAbs[i] != NO_ABS && $toAbs[i] == $r2[i]
   && ObjInv(i, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
  requires MsGcInv($ptr, HeapHi, $Time, $r1, $r2, $color, true, $GcMem, $toAbs, $AbsMem, $gcSlice);

  modifies $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $toAbs, $fs, $fn, $GcMem, CacheSize;

  ensures  esi == $_ptr;
  ensures  edi == $_prev;
  ensures  ebp == $_regionStart;
  ensures  GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $r1, $r2, $GcMem);
  ensures  ObjectSeq(HeapLo, $_regionStart, $toAbs, $fs, $fn);
  ensures  FreeInv(HeapLo, $_regionStart, $fs, $fn, $GcMem, CachePtr, CacheSize);
  ensures  Objects($_ptr, HeapHi, $toAbs, $fs, $fn);
  ensures  $fs[$_prev] != 0;
  ensures  $GcMem[$_prev] == 0;
  ensures  Aligned($_prev) && HeapLo <= $_prev && $_prev + 8 <= $_regionStart && $_regionStart <= $_ptr;
  ensures  $_ptr < HeapHi + 4;
  ensures  (forall ii:int::{TV(ii)} TV(ii) ==> HeapLo <= ii && ii < $_prev && $fs[ii] != 0 ==> $fn[ii] <= $_prev);
  ensures  (forall ii:int::{TV(ii)} TV(ii) ==> $_prev <= ii && ii < $_ptr && $fs[ii] != 0 ==> $fn[ii] == 0);
  ensures  (forall ii:int::{TV(ii)} TV(ii) ==> $_regionStart <= ii && ii < $_ptr ==> $toAbs[ii] == NO_ABS && $fs[ii] == 0);
  ensures  CacheSize == 0;
  ensures  HeapLo <= $_ptr;
  ensures  Aligned($_regionStart) && Aligned($_ptr);
  ensures  AllocInv2($toAbs, HeapLo, HeapHi, $r1, $r2, false);
  ensures  (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> $toAbs[i] != NO_ABS ==> !Gray($color[i]));
  ensures  (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < $_ptr ==> (White($color[i]) <==> $toAbs[i] != NO_ABS));
  ensures  (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < $_ptr && $toAbs[i] != NO_ABS ==>
      $r1[i] != NO_ABS && $r2[i] != NO_ABS
   && $toAbs[i] != NO_ABS && $toAbs[i] == $r2[i]
   && ObjInv(i, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
  ensures  MsGcInv($_ptr, HeapHi, $Time, $r1, $r2, $color, true, $GcMem, $toAbs, $AbsMem, $gcSlice);
{
  var size:int;
  var save1:int;
  var save2:int;
  var save3:int;

  assert TV(esi) && TV(ebp) && TV(edi) && TO(1);
  assert TO(numFields($toAbs[esi]));

  if (ebx != 3) { goto skip1; } // !black
    save1 := esi;
    save2 := edi;
    save3 := ebp;
    ecx := esi;
    call edx := GcLoad(esi + 4);
    esp := esp - 4; call GetSize($ptr, $GcMem[$ptr + 4], $r2, $r2);
    size := eax;
    assert size == 4 * numFields($toAbs[$ptr]);
    esi := save1;
    ebp := save3;

    call esi := Sub(esi, HeapLo);
    edi := ColorBase;
    edx := 1; // white
    call bb4SetColor($color, 1, HeapLo, HeapLo, HeapLo, HeapHi, $ptr, ColorBase, HeapLo);
    esi := save1;
    edi := save2;
    $color[esi] := 1; // white

    eax := esi;
    call eax := Sub(eax, ebp);
  // TUNING: min cache size
    if (eax < 256) { goto skipFree; }
//    if (eax < 1024) { goto skipFree; }
//    if (eax < 2048) { goto skipFree; }
      // Turn region into free block
      $fn[edi] := ebp;
      call GcStore(edi, ebp);
      $fn[ebp] := 0;
      $fs[ebp] := eax;
      call GcStore(ebp, 0);
      call GcStore(ebp + 4, eax);
      edi := ebp;
    skipFree:
    // Start a new region.
    call esi := Add(esi, size);
    ebp := esi;
    goto skip2;
  //else
  skip1:
    assert White($color[esi]);
    save1 := esi;
    save2 := edi;
    save3 := ebp;
    ecx := esi;
    call edx := GcLoad(esi + 4);
    esp := esp - 4; call GetSize($ptr, $GcMem[$ptr + 4], $r1, $r1);
    size := eax;
    assert size == 4 * numFields($toAbs[$ptr]);
    esi := save1;
    edi := save2;
    ebp := save3;

    $toAbs[esi] := NO_ABS;
    call esi := Sub(esi, HeapLo);
    edi := ColorBase;
    edx := 0; // unallocated
    call bb4SetColor($color, 0, HeapLo, HeapLo, HeapLo, HeapHi, $ptr, ColorBase, HeapLo);
    esi := save1;
    edi := save2;
    $color[esi] := 0; // unallocated

    call esi := Add(esi, size);
  skip2:
  $_ptr := esi;
  $_prev := edi;
  $_regionStart := ebp;
}

procedure Sweep()
  requires AllocInv2($toAbs, HeapLo, HeapHi, $r1, $r2, false);
  requires MsGcInv(HeapLo, HeapHi, $Time, $r1, $r2, $color, true, $GcMem, $toAbs, $AbsMem, $gcSlice);
  requires (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> $toAbs[i] != NO_ABS ==> !Gray($color[i]));
  requires (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> $toAbs[i] != NO_ABS && Black($color[i]) ==>
            $toAbs[i] == $r2[i]);
  requires GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $r1, $r2, $GcMem);
  requires $freshAbs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $freshAbs);
  requires Objects(HeapLo + 8, HeapHi, $toAbs, $fs, $fn);
  requires $fs[HeapLo] == 8;
  requires ObjectSeq(HeapLo, HeapLo + 8, $toAbs, $fs, $fn);
  requires FreeInv(HeapLo, HeapLo + 8, $fs, $fn, $GcMem, CachePtr, CacheSize);
  requires HeapLo + 8 <= HeapHi;

  modifies $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $toAbs, $fs, $fn, $GcMem, CacheSize;

  ensures  (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> $toAbs[i] != NO_ABS ==> reached($toAbs[i], $Time));
  ensures  MsInv(HeapLo, HeapHi, $color, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $r1, $r2, $GcMem);
  ensures  (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $freshAbs);
  ensures  ObjectSeq(HeapLo, HeapHi, $toAbs, $fs, $fn);
  ensures  FreeInv(HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize);
  ensures  $toAbs == $r2;
{
  // esi = ptr
  // edi = prev
  // ebp = regionStart
  var $_ptr:int;
  var $_prev:int;
  var $_regionStart:int;
  assert TV(HeapLo);
  assert TV(HeapLo + 8);

  CacheSize := 0;
  edi := HeapLo;
  call esi := Lea(edi + 8);
  ebp := esi;
  $fn[edi] := 0;
  assert TV(edi);
  call GcStore(edi, 0);

  //
  // ... [edi:free ... ] ... [ebp:empty ... ] esi
  // 

  //while (esi < HeapHi)
  loop:
    assert GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $r1, $r2, $GcMem);
    assert ObjectSeq(HeapLo, ebp, $toAbs, $fs, $fn);
    assert FreeInv(HeapLo, ebp, $fs, $fn, $GcMem, CachePtr, CacheSize);
    assert Objects(esi, HeapHi, $toAbs, $fs, $fn);
    assert $fs[edi] != 0;
    assert $GcMem[edi] == 0;
    assert Aligned(edi);
    assert HeapLo <= edi && edi + 8 <= ebp && ebp <= esi;
    assert esi < HeapHi + 4;
    assert (forall ii:int::{TV(ii)} TV(ii) ==> HeapLo <= ii && ii < edi && $fs[ii] != 0 ==> $fn[ii] <= edi);
    assert (forall ii:int::{TV(ii)} TV(ii) ==> edi <= ii && ii < esi && $fs[ii] != 0 ==> $fn[ii] == 0);
    assert (forall ii:int::{TV(ii)} TV(ii) ==> ebp <= ii && ii < esi ==> $toAbs[ii] == NO_ABS && $fs[ii] == 0);
    assert CacheSize == 0;

    assert HeapLo <= esi;
    assert Aligned(ebp) && Aligned(esi);
    assert AllocInv2($toAbs, HeapLo, HeapHi, $r1, $r2, false);
    assert (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> $toAbs[i] != NO_ABS ==> !Gray($color[i]));

    assert (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < esi ==> (White($color[i]) <==> $toAbs[i] != NO_ABS));
    assert (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < esi && $toAbs[i] != NO_ABS ==>
        $r1[i] != NO_ABS && $r2[i] != NO_ABS
     && $toAbs[i] != NO_ABS && $toAbs[i] == $r2[i]
     && ObjInv(i, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert MsGcInv(esi, HeapHi, $Time, $r1, $r2, $color, true, $GcMem, $toAbs, $AbsMem, $gcSlice);
    if (esi >= HeapHi) { goto loopEnd; }

    assert TV(esi) && TV(ebp) && TV(edi);

    ebx := esi;
    call ebx := Sub(ebx, HeapLo);
    eax := ColorBase;
    call bb4GetColor($color, HeapLo, HeapLo, HeapLo, HeapHi, esi, ColorBase, HeapLo);
    assert ebx == $color[esi];
    if (ebx == 0) { goto skip1; } // unallocated
      call $_ptr, $_prev, $_regionStart := sweepObject(esi, edi, ebp);
      goto loop;
    //else
    skip1:
      assert TO(1);
      call __notAligned(esi);
      $fs[esi] := 0;
      call esi := Add(esi, 4);
    goto loop;
  loopEnd:

  // don't forget the last region
  eax := esi;
  call eax := Sub(eax, ebp);
  // TUNING: min cache size
  if (eax < 256) { goto skip2; }
//  if (eax < 1024) { goto skip2; }
//  if (eax < 2048) { goto skip2; }
    // Turn region into free block
    $fn[edi] := ebp;
    call GcStore(edi, ebp);
    $fn[ebp] := 0;
    $fs[ebp] := esi - ebp;
    assert TV(ebp) && TO(1);
    call GcStore(ebp, 0);
    call GcStore(ebp + 4, eax);
    edi := ebp;
  skip2:

  call __notAligned(HeapHi);
  $toAbs := $r2;

  esp := esp + 4; return;
}

procedure GarbageCollect($ra:int, $nextFp:int)
  requires ecx == $ra && word($ra);
  requires edx == $nextFp;
  requires FrameNextInv($FrameCount, $ra, $nextFp, $FrameAddr, $FrameLayout);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  requires StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires $freshAbs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $freshAbs);

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $color, StackTop;
  modifies $fs, $fn, CacheSize;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  // postcondition same as precondition, plus reached:
  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $freshAbs);
  ensures  (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi && $toAbs[i] != NO_ABS ==>
             reached($toAbs[i], $Time));
  ensures  ebp == old(ebp);
{
  var saveEbp:int;
  saveEbp := ebp;

  $r1 := $toAbs;
  $r2 := MAP_NO_ABS;

  eax := ?gcLo;
  StackTop := eax;
  call scanStack($ra, $nextFp);
  call scanStatic();
  call processMarkStack();

  assert TV(HeapLo);
  $fn[HeapLo] := 0;
  eax := HeapLo;
  call GcStore(eax, 0);
  CacheSize := 0;

  esp := esp - 4; call Sweep();

  ebp := saveEbp;
  esp := esp + 4; return;
}

procedure allocObjectMemory($ra:int, $nextFp:int, $size:int, $nFields:int)
  requires eax == $size;
  requires ecx == $ra && word($ra);
  requires edx == $nextFp;
  requires FrameNextInv($FrameCount, $ra, $nextFp, $FrameAddr, $FrameLayout);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  requires StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires 8 <= $size;
  requires $size == 4 * $nFields;
  requires $freshAbs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> $toAbs[i] != $freshAbs);

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $color, StackTop;
  modifies $fs, $fn, CachePtr, CacheSize, ReserveMin;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  $fs[eax] >= $size;
  ensures  HeapLo < eax && eax + $size <= HeapHi;
  ensures  Disconnected(HeapLo, eax, $fs, $fn);
  ensures  CacheSize != 0 ==> eax != CachePtr;
  ensures  Aligned(eax);
  ensures  (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi ==> $toAbs[i] != $freshAbs);
{
  var ra:int;
  var nextFp:int;
  var size:int;
  ra := ecx;

  ecx := eax;
  call eax := AddChecked(eax, 8);
  if (eax > CacheSize) { goto skip1; }
    call allocFromCache($size, $nFields);
    goto end;
  //else
  skip1:
    nextFp := edx;
    size := ecx;
    esp := esp - 4; call AllocSlow($size, $nFields);
    if (eax != 0) { goto end; }
      ecx := ra; // $ra && word($ra);
      edx := nextFp; // $nextFp;

      esp := esp - 4; call GarbageCollect($ra, $nextFp);
      ecx := size;
      esp := esp - 4; call AllocSlow($size, $nFields);
      if (eax != 0) { goto end; }
        // Try using some of the reserve:
        ecx := size;
        call ReserveMin := SubChecked(ReserveMin, ecx);
        // TUNING: wilderness policy // REVIEW: this should be a parameter, not hard-wired into the code
        call ReserveMin := SubChecked(ReserveMin, 1048576); // Bartok,Zinger
//        call ReserveMin := SubChecked(ReserveMin, 65536); // Sat
        esp := esp - 4; call AllocSlow($size, $nFields);
        if (eax != 0) { goto end; }
          // out of memory
          call DebugBreak();
  end:
}

procedure doAllocWord($ret:int, $ind:int, $nf:int)
  requires esi == $ret + 4 * $ind;

  requires TO($ind) && $ind >= 0 && $ind < $nf;
  requires Aligned($ret) && HeapLo <= $ret && $ret + 4 * $ind + 4 <= HeapHi;
  requires MsInv(HeapLo, HeapHi, $color, $GcMem, $toAbs, $AbsMem, $gcSlice);
  requires GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $toAbs, $toAbs, $GcMem);
  requires ObjectSeq(HeapLo, HeapHi, $toAbs, $fs, $fn);
  requires FreeInvBase(HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize);
  requires (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi && $fs[i] != 0 && i != $ret ==>
             FreeInvI(i, HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize));
  requires (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> $gcSlice[$ret + 4 * j] == $ret);
  requires (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> gcAddr($ret + 4 * j)); // REVIEW: necessary?
  requires (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> $GcMem[$ret + 4 * j] == NULL);
  requires $fs[$ret] >= 4 * $nf;
  requires CacheSize != 0 ==> $ret != CachePtr;
  requires Disconnected(HeapLo, $ret, $fs, $fn);

  modifies $GcMem, $gcSlice;

  ensures  MsInv(HeapLo, HeapHi, $color, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $toAbs, $toAbs, $GcMem);
  ensures  ObjectSeq(HeapLo, HeapHi, $toAbs, $fs, $fn);
  ensures  FreeInvBase(HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize);
  ensures  (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi && $fs[i] != 0 && i != $ret ==>
             FreeInvI(i, HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize));
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind + 1 ==> $gcSlice[$ret + 4 * j] == $ret);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind + 1 ==> gcAddr($ret + 4 * j)); // REVIEW: necessary?
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind + 1 ==> $GcMem[$ret + 4 * j] == NULL);
  ensures  ebp == old(ebp);
{
  assert TV($ret);
  assert TV($ret + 4 * $ind);// && TV($ret + 4 * $ind + 1) && TV($ret + 4 * $ind + 2) && TV($ret + 4 * $ind + 3);
  $gcSlice[$ret + 4 * $ind] := $ret;

  call GcStore(esi, 0);
}

procedure doAllocWords($ret:int, $size:int, $nf:int)
  requires eax == $ret;
  requires ebx == $ret + $size;
  requires $size == $nf * 4;
  requires $nf >= 0;
  requires Aligned($ret) && HeapLo <= $ret && $ret + $size <= HeapHi;
  requires MsInv(HeapLo, HeapHi, $color, $GcMem, $toAbs, $AbsMem, $gcSlice);
  requires GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $toAbs, $toAbs, $GcMem);
  requires ObjectSeq(HeapLo, HeapHi, $toAbs, $fs, $fn);
  requires FreeInvBase(HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize);
  requires (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi && $fs[i] != 0 && i != $ret ==>
             FreeInvI(i, HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize));
  requires $fs[$ret] >= 4 * $nf;
  requires CacheSize != 0 ==> $ret != CachePtr;
  requires Disconnected(HeapLo, $ret, $fs, $fn);

  modifies $GcMem, $gcSlice;
  modifies esi;

  ensures  MsInv(HeapLo, HeapHi, $color, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $toAbs, $toAbs, $GcMem);
  ensures  ObjectSeq(HeapLo, HeapHi, $toAbs, $fs, $fn);
  ensures  FreeInvBase(HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize);
  ensures  (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi && $fs[i] != 0 && i != $ret ==>
             FreeInvI(i, HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize));
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $nf ==> $gcSlice[$ret + 4 * j] == $ret);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $nf ==> gcAddr($ret + 4 * j)); // REVIEW: necessary?
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $nf ==> $GcMem[$ret + 4 * j] == NULL);
  ensures  ebp == old(ebp);
{
  var $ind:int;
  $ind := 0;

  esi := ?gcLo;
  esi := eax;

  //while (4 * $ind < $size)
  if (esi >= ebx) { goto loopEnd; }
  loop:
    assert 4 * $ind < $size;
    assert esi == $ret + 4 * $ind;
    assert TO($ind) && $ind >= 0;
    assert  MsInv(HeapLo, HeapHi, $color, $GcMem, $toAbs, $AbsMem, $gcSlice);
    assert  GcInv(ColorBase, HeapLo, HeapHi, $color, $toAbs, $toAbs, $toAbs, $GcMem);
    assert  ObjectSeq(HeapLo, HeapHi, $toAbs, $fs, $fn);
    assert  FreeInvBase(HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize);
    assert  (forall i:int::{TV(i)} TV(i) ==> HeapLo <= i && i < HeapHi && $fs[i] != 0 && i != $ret ==>
               FreeInvI(i, HeapLo, HeapHi, $fs, $fn, $GcMem, CachePtr, CacheSize));
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> $gcSlice[$ret + 4 * j] == $ret);
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> gcAddr($ret + 4 * j)); // REVIEW: necessary?
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> $GcMem[$ret + 4 * j] == NULL);

    call doAllocWord($ret, $ind, $nf);
    $ind := $ind + 1;
    call esi := Add(esi, 4);
    if (esi < ebx) { goto loop; }
  loopEnd:
}

procedure doAllocObject($ra:int, $nextFp:int, $ptr:int, $abs:int, $vt:int, $size:int)
  requires eax == $ptr;
  requires ebx == $ptr + $size;
  requires ecx == $vt;
  requires HeapLo < $ptr && $ptr + 4 * numFields($abs) <= HeapHi && Aligned($ptr);
  requires !VFieldPtr($abs, 0);
  requires !VFieldPtr($abs, 1);
  requires 2 <= numFields($abs);
  requires $size == 4 * numFields($abs);
  requires ObjSize($abs, $vt, $AbsMem[$abs][2], $AbsMem[$abs][3]);
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires $fs[$ptr] >= 4 * numFields($abs);
  requires CacheSize != 0 ==> $ptr != CachePtr;
  requires Disconnected(HeapLo, $ptr, $fs, $fn);

  // requirements on vtable and layout:
  requires word($vt) && !gcAddrEx($vt);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, 0, 0);
  requires !isVarSize(tag($vt));

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires (forall j:int::{TO(j)} TO(j) ==> 2 <= j && j < numFields($abs) ==> $AbsMem[$abs][j] == NULL);

  modifies $GcMem, $toAbs, $gcSlice, $fs, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  old($toAbs)[eax - 4] == NO_ABS;
  ensures  $toAbs == old($toAbs)[eax - 4 := $abs];
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  ebp == old(ebp);
{
  assert TV($ptr) && TV($fn[$ptr]);

  assert TV(eax + 0) && TV(eax + 4);
  assert TO(1) && TO(2);
  assert TO(numFields($abs));

  call doAllocWords(eax, $size, numFields($abs));

  call GcStore(eax + 4, ecx);

  $toAbs[$ptr] := $abs;
  ebx := eax;
  esi := eax;
  call esi := Sub(esi, HeapLo);
  edi := ColorBase;
  edx := 1; // white
  call bb4SetColor($color, 1, HeapLo, HeapLo, HeapLo, HeapHi, $ptr, ColorBase, HeapLo);
  $color[$ptr] := 1; // white
  $fs[$ptr] := 0;

  assert TO(numFields($abs));

  call eax := Lea(ebx + 4);

  assert TV(eax + 4);
  assert TO(0);
}

procedure doAllocString($ra:int, $nextFp:int, $ptr:int, $abs:int, $vt:int, $nElems:int)
  requires eax == $ptr;
  requires ebx == $ptr + pad(16 + 2 * $nElems);
  requires ecx == pad(16 + 2 * $nElems);
  requires edx == $nElems;
  requires $vt == ?STRING_VTABLE;
  requires $ptr + pad(16 + 2 * $nElems) + 0 <= HeapHi;

  requires HeapLo < $ptr && $ptr + 4 * numFields($abs) <= HeapHi && Aligned($ptr);
  requires !VFieldPtr($abs, 0);
  requires !VFieldPtr($abs, 1);
  requires 2 <= numFields($abs);
  requires ObjSize($abs, $vt, $AbsMem[$abs][2], $AbsMem[$abs][3]);
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires $fs[$ptr] >= 4 * numFields($abs);
  requires CacheSize != 0 ==> $ptr != CachePtr;
  requires Disconnected(HeapLo, $ptr, $fs, $fn);

  // requirements on vtable and layout:
  requires word($vt) && !gcAddrEx($vt);
  requires word($nElems);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $nElems, 0);
  requires tag($vt) == ?STRING_TAG;

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires $AbsMem[$abs][2] == $nElems;
  requires $AbsMem[$abs][3] == $nElems - 1;
  requires (forall j:int::{TO(j)} TO(j) ==> 4 <= j && 4 * j < pad(16 + 2 * $nElems) ==> $AbsMem[$abs][j] == NULL);

  modifies $GcMem, $toAbs, $gcSlice, $fs, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  old($toAbs)[eax - 4] == NO_ABS;
  ensures  $toAbs == old($toAbs)[eax - 4 := $abs];
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  ebp == old(ebp);
{
  assert TV(eax + 0) && TV(eax + 4) && TV(eax + 8) && TV(eax + 12);
  assert TO(1) && TO(2) && TO(3);
  assert TVL($abs);
  assert TVT($abs, $vt);
  assert TO(numFields($abs));

  call doAllocWords(eax, pad(16 + 2 * $nElems), numFields($abs));

  call GcStore(eax + 8, edx);
  call edx := SubChecked(edx, 1);
  call GcStore(eax + 12, edx);
  edx := ?STRING_VTABLE;
  call GcStore(eax + 4, edx);

  $toAbs[$ptr] := $abs;
  ebx := eax;
  esi := eax;
  call esi := Sub(esi, HeapLo);
  edi := ColorBase;
  edx := 1; // white
  call bb4SetColor($color, 1, HeapLo, HeapLo, HeapLo, HeapHi, $ptr, ColorBase, HeapLo);
  $color[$ptr] := 1; // white
  $fs[$ptr] := 0;

  assert TO(numFields($abs));

  call eax := Lea(ebx + 4);

  assert TV(eax + 4);
  assert TO(0);
}

procedure doAllocArrayHelper($abs:int, $vt:int, $rank:int, $nElems:int)
  requires ecx == $vt;
  requires esi == $nElems;
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $rank, $nElems);
  requires tag($vt) == ?PTR_ARRAY_TAG || tag($vt) == ?OTHER_ARRAY_TAG;
  modifies eax, ebx, edx, edi;
  ensures  !VFieldPtr($abs, 0);
  ensures  !VFieldPtr($abs, 1);
  ensures  !VFieldPtr($abs, 2);
  ensures  !VFieldPtr($abs, 3);
  ensures  between(4, numFields($abs), baseWords($vt));
  ensures  eax == 4 * numFields($abs);
{
  assert TO(2) && TO(3);
  assert TVL($abs);
  assert TVT($abs, $vt);

  call eax := RoLoad32(ecx + ?VT_BASE_LENGTH);
  call ebx := RoLoad32(ecx + ?VT_ARRAY_ELEMENT_SIZE);
  call edi := RoLoad32(ecx + ?VT_MASK);
  call edi := And(edi, 15);

  //if (edi == ?PTR_ARRAY_TAG)
  if (edi != ?PTR_ARRAY_TAG) { goto skip1; }
    edi := esi;
    call edi := AddChecked(edi, edi);
    call edi := AddChecked(edi, edi);
    call eax := AddChecked(eax, edi);
    call eax := AddChecked(eax, 3);
    edi := 3;
    call edi := Not(edi);
    call eax := And(eax, edi);
    goto skip2;
  //else
  skip1:
    edi := eax;
    eax := ebx;
    call eax, edx := MulChecked(eax, esi);
    call eax := AddChecked(eax, edi);
    call eax := AddChecked(eax, 3);
    edi := 3;
    call edi := Not(edi);
    call eax := And(eax, edi);
  skip2:
}

procedure doAllocArray($ra:int, $nextFp:int, $ptr:int, $abs:int, $vt:int, $rank:int, $nElems:int, $size:int)
  requires eax == $ptr;
  requires ebx == $ptr + $size;
  requires ecx == $vt;
  requires edx == $rank;
  requires esi == $nElems;
  requires HeapLo < $ptr && $ptr + 4 * numFields($abs) <= HeapHi && Aligned($ptr);
  requires !VFieldPtr($abs, 0);
  requires !VFieldPtr($abs, 1);
  requires !VFieldPtr($abs, 2);
  requires !VFieldPtr($abs, 3);
  requires 4 <= numFields($abs);
  requires $size == 4 * numFields($abs);
  requires ObjSize($abs, $vt, $rank, $nElems);
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires $fs[$ptr] >= 4 * numFields($abs);
  requires CacheSize != 0 ==> $ptr != CachePtr;
  requires Disconnected(HeapLo, $ptr, $fs, $fn);

  // requirements on vtable and layout:
  requires word($vt) && !gcAddrEx($vt);
  requires word($rank);
  requires word($nElems);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $rank, $nElems);
  requires tag($vt) == ?PTR_ARRAY_TAG || tag($vt) == ?OTHER_ARRAY_TAG;

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires $AbsMem[$abs][2] == $rank;
  requires $AbsMem[$abs][3] == $nElems;
  requires (forall j:int::{TO(j)} TO(j) ==> 4 <= j && j < numFields($abs) ==> $AbsMem[$abs][j] == NULL);

  modifies $GcMem, $toAbs, $gcSlice, $fs, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  old($toAbs)[eax - 4] == NO_ABS;
  ensures  $toAbs == old($toAbs)[eax - 4 := $abs];
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  ebp == old(ebp);
{
  var nElems:int;
  nElems := esi;

  assert TV(eax + 0) && TV(eax + 4) && TV(eax + 8) && TV(eax + 12);
  assert TO(1) && TO(2) && TO(3) && TO(4);
  assert TO(numFields($abs));

  call doAllocWords(eax, $size, numFields($abs));

  esi := nElems;
  call GcStore(eax + 4, ecx);
  call GcStore(eax + 8, edx);
  call GcStore(eax + 12, esi);

  $toAbs[$ptr] := $abs;
  ebx := eax;
  esi := eax;
  call esi := Sub(esi, HeapLo);
  edi := ColorBase;
  edx := 1; // white
  call bb4SetColor($color, 1, HeapLo, HeapLo, HeapLo, HeapHi, $ptr, ColorBase, HeapLo);
  $color[$ptr] := 1; // white
  $fs[$ptr] := 0;

  assert TO(numFields($abs));

  call eax := Lea(ebx + 4);

  assert TV(eax + 4);
  assert TO(0);
}

procedure doAllocVectorHelper($abs:int, $vt:int, $nElems:int)
  requires ecx == $vt;
  requires edx == $nElems;
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $nElems, 0);
  requires tag($vt) == ?PTR_VECTOR_TAG || tag($vt) == ?OTHER_VECTOR_TAG;
  modifies eax, ebx, edx, esi, edi;
  ensures  !VFieldPtr($abs, 0);
  ensures  !VFieldPtr($abs, 1);
  ensures  !VFieldPtr($abs, 2);
  ensures  3 <= numFields($abs);
  ensures  eax == 4 * numFields($abs);
  ensures  ObjSize($abs, $vt, $nElems, $AbsMem[$abs][3]);
{
  assert TO(2);
  assert TVL($abs);
  assert TVT($abs, $vt);

  call eax := RoLoad32(ecx + ?VT_BASE_LENGTH);
  call ebx := RoLoad32(ecx + ?VT_ARRAY_ELEMENT_SIZE);
  call edi := RoLoad32(ecx + ?VT_MASK);
  call edi := And(edi, 15);

  //if (edi == ?PTR_ARRAY_TAG)
  if (edi != ?PTR_VECTOR_TAG) { goto skip1; }
    edi := edx;
    call edi := AddChecked(edi, edi);
    call edi := AddChecked(edi, edi);
    call eax := AddChecked(eax, edi);
    call eax := AddChecked(eax, 3);
    edi := 3;
    call edi := Not(edi);
    call eax := And(eax, edi);
    goto skip2;
  //else
  skip1:
    edi := eax;
    eax := ebx;
    call eax, edx := MulChecked(eax, edx);
    call eax := AddChecked(eax, edi);
    call eax := AddChecked(eax, 3);
    edi := 3;
    call edi := Not(edi);
    call eax := And(eax, edi);
  skip2:
}

procedure doAllocVector($ra:int, $nextFp:int, $ptr:int, $abs:int, $vt:int, $nElems:int, $size:int)
  requires eax == $ptr;
  requires ebx == $ptr + $size;
  requires ecx == $vt;
  requires edx == $nElems;
  requires HeapLo < $ptr && $ptr + 4 * numFields($abs) <= HeapHi && Aligned($ptr);
  requires !VFieldPtr($abs, 0);
  requires !VFieldPtr($abs, 1);
  requires !VFieldPtr($abs, 2);
  requires 3 <= numFields($abs);
  requires $size == 4 * numFields($abs);
  requires ObjSize($abs, $vt, $nElems, $AbsMem[$abs][3]);
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires $fs[$ptr] >= 4 * numFields($abs);
  requires CacheSize != 0 ==> $ptr != CachePtr;
  requires Disconnected(HeapLo, $ptr, $fs, $fn);

  // requirements on vtable and layout:
  requires word($vt) && !gcAddrEx($vt);
  requires word($nElems);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $nElems, 0);
  requires tag($vt) == ?PTR_VECTOR_TAG || tag($vt) == ?OTHER_VECTOR_TAG;

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires $AbsMem[$abs][2] == $nElems;
  requires (forall j:int::{TO(j)} TO(j) ==> 3 <= j && j < numFields($abs) ==> $AbsMem[$abs][j] == NULL);

  modifies $GcMem, $toAbs, $gcSlice, $fs, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  old($toAbs)[eax - 4] == NO_ABS;
  ensures  $toAbs == old($toAbs)[eax - 4 := $abs];
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  ebp == old(ebp);
{
  assert TV(eax + 0) && TV(eax + 4) && TV(eax + 8);
  assert TO(1) && TO(2) && TO(3);
  assert TO(numFields($abs));

  call doAllocWords(eax, $size, numFields($abs));

  call GcStore(eax + 4, ecx);
  call GcStore(eax + 8, edx);


  $toAbs[$ptr] := $abs;
  ebx := eax;
  esi := eax;
  call esi := Sub(esi, HeapLo);
  edi := ColorBase;
  edx := 1; // white
  call bb4SetColor($color, 1, HeapLo, HeapLo, HeapLo, HeapHi, $ptr, ColorBase, HeapLo);
  $color[$ptr] := 1; // white
  $fs[$ptr] := 0;

  assert TO(numFields($abs));

  call eax := Lea(ebx + 4);

  assert TV(eax + 4);
  assert TO(0);
}

//////////////////////////////////////////////////////////////////////////////
//
// The procedures below are the entry points from the mutator.
//
// Therefore, the requires, ensures, and modifies clauses for these procedures
// are part of the trusted computing base!
//
//////////////////////////////////////////////////////////////////////////////

procedure Initialize()
  modifies $toAbs, $color;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $GcMem, HeapLo, HeapHi, ColorBase, $fn, $fs, CacheSize, ReserveMin;
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  ebp == old(ebp);
  ensures  WellFormed($toAbs);
{
  var save:int;
  var unitSize:int;
  save := ebp;

  // The gc memory consists a mark stack, a color bit map, and a heap:
  //   <--4--><--4--><--64-->
  // The bit map must consist of a multiple of 4 bytes.
  // For each 2 bits in the bit map, there is one word in the heap.

  // In the worst case, the mark stack could have as many words
  // as there are pointed-to objects in memory.  Since an
  // object requires at least 2 words (preheader, header), and
  // a pointer requires 1 word, this means that the mark stack
  // might need to be as big as 1/3 the heap size: 64 / 3 >= 22.
  // We're more optimistic; we pick 1/16 the heap size: 64 / 16 = 4.

  // Thus, the total gc memory size must be a multiple of:
  //   4 + 4 + 64 = 72 bytes

  // Compute gcMem size, in bytes and words
  esi := ?gcHi;
  call esi := Sub(esi, ?gcLo);
  edi := esi;

  // Break into 72-byte units.  Let ebp be the number of units.
  edx := 0;
  eax := edi;
  ebx := 72;
  call eax, edx := Div(eax, edx, ebx);
  ebp := eax;
  unitSize := ebp;
  assert 72 * unitSize <= (?gcHi - ?gcLo);

  if (ebp != 0) { goto skip1; }
    // not enough space for heap data structures
    call DebugBreak();
  skip1:

  // Divide heap into ?gcLo <--4--> eax <--4--> ebx <--64--> ecx <--> ?gcHi
  edx := 0;
  call ebp := Lea(edx + 4 * ebp);
  eax := ?gcLo;
  call eax := Add(eax, ebp);
  ColorBase := eax;
//assert ColorBase == ?gcLo + 4 * unitSize;
  call ebx := Lea(eax + ebp);
  HeapLo := ebx;
//assert HeapLo == ?gcLo + 8 * unitSize;
  call ebp := Lea(edx + 4 * ebp);
  call ecx := Lea(ebx + 4 * ebp);
  HeapHi := ecx;
//assert HeapHi == ?gcLo + 72 * unitSize;

  $toAbs := MAP_NO_ABS;

  assert TV(?gcLo);
  assert TV(ColorBase);
  assert TV(HeapLo);
  assert TV(HeapLo + 8);
  assert TV(HeapHi);
  assert TO(0);
  assert TO(1);
  assert TO(2);
  assert TO(3);
  assert TO(unitSize);
  assert TO(2 * unitSize);
  assert TO(16 * unitSize);

  $fs := MAP_ZERO;
  $fn := MAP_ZERO;
  $color := MAP_ZERO;
  eax := ColorBase;
  ebx := HeapLo;

//assert Aligned(ColorBase);
//assert Aligned(HeapLo);
//assert HeapHi - HeapLo == 16 * (HeapLo - ColorBase);

  esp := esp - 4; call BB4Zero2($color, HeapLo, HeapLo, HeapLo, HeapHi, 0, ColorBase, HeapLo, 0, 0);

  $fn[HeapLo] := HeapLo + 8;
  $fs[HeapLo] := 8;
  eax := HeapLo;
  call ebx := Lea(eax + 8);
  call GcStore(eax, ebx);
  call GcStore(eax + 4, 8);
  $fs[HeapLo + 8] := HeapHi - (HeapLo + 8);
  $fn[HeapLo + 8] := 0;
  call GcStore(eax + 8, 0);
  ecx := HeapHi;
  call ecx := Sub(ecx, ebx);
  call GcStore(eax + 12, ecx);
  CacheSize := 0;

  eax := HeapLo;
  // TUNING: wilderness size  // REVIEW: this should be a parameter, not hard-wired into the code
//  call eax := AddChecked(eax, 128000000); // Bartok
//  call eax := AddChecked(eax, 8000000); // Zinger, Sat
  ReserveMin := eax;

  ebp := save;
  esp := esp + 4; return;
}

// Prepare to call GcLoad (don't actually call it -- let the mutator call it)
procedure readField($ptr:int, $fld:int) returns ($val:int)
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires Pointer($toAbs, $ptr, $toAbs[$ptr]);
  requires 0 <= $fld && $fld < numFields($toAbs[$ptr]);
  ensures  gcAddr($ptr + 4 * $fld);
  ensures  $val == $GcMem[$ptr + 4 * $fld];
  ensures  Value(VFieldPtr($toAbs[$ptr], $fld), $toAbs, $val, $AbsMem[$toAbs[$ptr]][$fld]);
{
//  call $val := GcLoad($ptr + 4 * $fld);
  $val := $GcMem[$ptr + 4 * $fld];
  assert TV($val) && TV($ptr);
  assert TO($fld);
}

// Prepare to call GcStore (don't actually call it -- let the mutator call it)
procedure writeField($ptr:int, $fld:int, $val:int, $abs:int) returns ($_gcData:[int]int, $_absData:[int][int]int)
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  requires Pointer($toAbs, $ptr, $toAbs[$ptr]);
  requires 0 <= $fld && $fld < numFields($toAbs[$ptr]);
  requires !isReadonlyField(tag($AbsMem[$toAbs[$ptr]][1]), $fld);
  requires Value(VFieldPtr($toAbs[$ptr], $fld), $toAbs, $val, $abs);
  ensures  gcAddr($ptr + 4 * $fld);
  ensures  word($val);
  ensures  $_gcData == $GcMem[$ptr + 4 * $fld := $val];
  ensures  $_absData == $AbsMem[$toAbs[$ptr] := $AbsMem[$toAbs[$ptr]][$fld := $abs]];
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $_absData, $_gcData, $gcSlice, CachePtr, CacheSize);
{
//  call GcStore($ptr + 4 * $fld, $val);
//  call AbsEdgeWrite($ptr, $fld, $val);
  $_gcData := $GcMem[$ptr + 4 * $fld := $val];
  $_absData := $AbsMem[$toAbs[$ptr] := $AbsMem[$toAbs[$ptr]][$fld := $abs]];
  assert TVL($toAbs[$ptr]);
  assert TV($val) && TV($ptr);
  assert TO($fld);
//  assert TO(1);
}

procedure AllocObject($ra:int, $abs:int, $vt:int)
  // GC invariant:
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);

  // requirements on mutator root layout:
  requires 0 <= $FrameCount;
  requires $FrameSlice[esp] == $FrameCount && $FrameMem[esp] == $ra;
  requires FrameNextInv($FrameCount, $ra, ebp, $FrameAddr, $FrameLayout);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  requires StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);

  // requirements on vtable and layout:
  requires ecx == $vt;
  requires word($vt) && !gcAddrEx($vt);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, 0, 0);
  requires !isVarSize(tag($vt));

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires (forall j:int::{TO(j)} TO(j) ==> 2 <= j && j < numFields($abs) ==> $AbsMem[$abs][j] == NULL);

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $color, StackTop, $freshAbs;
  modifies $fs, $fn, CachePtr, CacheSize, ReserveMin;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
{
  var vt:int;
  var fp:int;
  var size:int;
  fp := ebp;
  vt := ecx;
  $freshAbs := $abs;

  assert TO(2);
  assert TVL($abs);
  assert TVT($abs, $vt);
  call eax := RoLoad32(ecx + ?VT_BASE_LENGTH);
  size := eax;

  call ecx := FrameLoad(($FrameCount), esp);
  edx := ebp;
  call allocObjectMemory($ra, fp, 4 * numFields($abs), numFields($abs));

  edx := size;
  call ebx := Lea(eax + edx);
  ecx := vt;
  call doAllocObject($ra, fp, eax, $abs, vt, 4 * numFields($abs));

  ebp := fp;
  esp := esp + 4; return;
}

procedure AllocString($ra:int, $abs:int, $vt:int, $nElems:int)
  // GC invariant:
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);

  // requirements on mutator root layout:
  requires 0 <= $FrameCount;
  requires $FrameSlice[esp] == $FrameCount && $FrameMem[esp] == $ra;
  requires FrameNextInv($FrameCount, $ra, ebp, $FrameAddr, $FrameLayout);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  requires StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);

  // requirements on vtable and layout:
  requires ecx == $nElems - 1;
  requires $vt == ?STRING_VTABLE;
  requires word($vt) && !gcAddrEx($vt);
  requires word($nElems);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $nElems, 0);
  requires tag($vt) == ?STRING_TAG;

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires $AbsMem[$abs][2] == $nElems;
  requires $AbsMem[$abs][3] == $nElems - 1;
  requires (forall j:int::{TO(j)} TO(j) ==> 4 <= j && 4 * j < pad(16 + 2 * $nElems) ==> $AbsMem[$abs][j] == NULL);

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $color, StackTop, $freshAbs;
  modifies $fs, $fn, CachePtr, CacheSize, ReserveMin;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
{
  var fp:int;
  var size:int;
  var nElems:int;
  fp := ebp;
  $freshAbs := $abs;

  assert TO(2);
  assert TVL($abs);
  assert TVT($abs, $vt);
  call ecx := AddChecked(ecx, 1);
  edx := ecx;
  nElems := edx;
  call ecx := AddChecked(ecx, ecx);
  call ecx := AddChecked(ecx, 19);
  eax := 3;
  call eax := Not(eax);
  call ecx := And(ecx, eax);
  size := ecx;
  eax := ecx;

  call ecx := FrameLoad(($FrameCount), esp);
  edx := ebp;
  call allocObjectMemory($ra, fp, 4 * numFields($abs), numFields($abs));

  edx := nElems;
  ecx := size;
  call ebx := Lea(eax + ecx);
  call doAllocString($ra, fp, eax, $abs, ?STRING_VTABLE, $nElems);

  ebp := fp;
  esp := esp + 4; return;
}

procedure AllocArray($ra:int, $abs:int, $vt:int, $rank:int, $nElems:int)
  // GC invariant:
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);

  // requirements on mutator root layout:
  requires 0 <= $FrameCount;
  requires $FrameSlice[esp] == $FrameCount && $FrameMem[esp] == $ra;
  requires FrameNextInv($FrameCount, $ra, ebp, $FrameAddr, $FrameLayout);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  requires StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);

  // requirements on vtable and layout:
  requires ecx == $vt;
  requires edx == $rank;
  requires $FrameSlice[esp + 4] == $FrameCount && $FrameMem[esp + 4] == $nElems;
  requires word($vt) && !gcAddrEx($vt);
  requires word($rank);
  requires word($nElems);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $rank, $nElems);
  requires tag($vt) == ?PTR_ARRAY_TAG || tag($vt) == ?OTHER_ARRAY_TAG;

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires $AbsMem[$abs][2] == $rank;
  requires $AbsMem[$abs][3] == $nElems;
  requires (forall j:int::{TO(j)} TO(j) ==> 4 <= j && j < numFields($abs) ==> $AbsMem[$abs][j] == NULL);

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $color, StackTop, $freshAbs;
  modifies $fs, $fn, CachePtr, CacheSize, ReserveMin;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
{
  var vt:int;
  var rank:int;
  var size:int;
  var nElems:int;
  var fp:int;

  $freshAbs := $abs;
  rank := edx;
  fp := ebp;
  vt := ecx;
  call esi := FrameLoad(($FrameCount), esp + 4);
  nElems := esi;

  call doAllocArrayHelper($abs, $vt, $rank, $nElems);
  size := eax;

  call ecx := FrameLoad(($FrameCount), esp);
  edx := ebp;
  call allocObjectMemory($ra, fp, 4 * numFields($abs), numFields($abs));

  edx := size;
  call ebx := Lea(eax + edx);
  edx := rank;
  esi := nElems;
  ecx := vt;
  call doAllocArray($ra, fp, eax, $abs, vt, $rank, $nElems, 4 * numFields($abs));

  ebp := fp;
  esp := esp + 4; return;
}

procedure AllocVector($ra:int, $abs:int, $vt:int, $nElems:int)
  // GC invariant:
  requires MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);

  // requirements on mutator root layout:
  requires 0 <= $FrameCount;
  requires $FrameSlice[esp] == $FrameCount && $FrameMem[esp] == $ra;
  requires FrameNextInv($FrameCount, $ra, ebp, $FrameAddr, $FrameLayout);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  requires StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);

  // requirements on vtable and layout:
  requires ecx == $vt;
  requires edx == $nElems;
  requires word($vt) && !gcAddrEx($vt);
  requires word($nElems);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $nElems, 0);
  requires tag($vt) == ?PTR_VECTOR_TAG || tag($vt) == ?OTHER_VECTOR_TAG;

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires $AbsMem[$abs][2] == $nElems;
  requires (forall j:int::{TO(j)} TO(j) ==> 3 <= j && j < numFields($abs) ==> $AbsMem[$abs][j] == NULL);

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $color, StackTop, $freshAbs;
  modifies $fs, $fn, CachePtr, CacheSize, ReserveMin;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(ColorBase, HeapLo, HeapHi, $color, $fs, $fn, $toAbs,
             $AbsMem, $GcMem, $gcSlice, CachePtr, CacheSize);
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
{
  var vt:int;
  var size:int;
  var nElems:int;
  var fp:int;

  $freshAbs := $abs;
  fp := ebp;
  vt := ecx;
  nElems := edx;

  call doAllocVectorHelper($abs, $vt, $nElems);
  size := eax;

  call ecx := FrameLoad(($FrameCount), esp);
  edx := ebp;
  call allocObjectMemory($ra, fp, 4 * numFields($abs), numFields($abs));

  edx := size;
  call ebx := Lea(eax + edx);
  edx := nElems;
  ecx := vt;
  call doAllocVector($ra, fp, eax, $abs, vt, $nElems, 4 * numFields($abs));

  ebp := fp;
  esp := esp + 4; return;
}


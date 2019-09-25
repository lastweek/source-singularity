//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// Verified copying garbage collector
//
// medium term goal: support more Bartok array-of-struct and vector-of-struct object layouts
// medium term goal: make generational
// long term goal: support various other features: threads, pinning, stack markers, etc.

// Imports:
//   - Trusted.bpl
//   - VerifiedBitVectors.bpl
// Includes:
//   - VerifiedCommon.bpl

// \Spec#\bin\Boogie.exe /noinfer Trusted.bpl VerifiedBitVectors.bpl VerifiedCommon.bpl VerifiedCopyingCollector.bpl

/*****************************************************************************
******************************************************************************
**** VERIFIED
******************************************************************************
*****************************************************************************/

//////////////////////////////////////////////////////////////////////////////
// COPYING COLLECTOR
//////////////////////////////////////////////////////////////////////////////

function IsFwdPtr(i:int) returns(bool) { gcAddrEx(i) }

var $freshAbs:int;

// The allocation bitmap ranges from ?gcLo..HeapLo
// The spaces (from and to) range from HeapLo..?gcHi
var HeapLo:int;
// Fromspace ranges from Fi to Fl, where Fk..Fl is empty
//   Tospace ranges from Ti to Tl, where Tk..Tl is empty
var Fi:int;
var Fk:int;
var Fl:int;
var Ti:int;
var Tj:int;
var Tk:int;
var Tl:int;
// Bitmaps for fromspace and tospace:
var BF:int;
var BT:int;

function ObjectSpc(i1:int, i2:int, r:[int]int) returns (bool)
{
  (forall i:int::{TV(i)} TV(i) ==> i1 <= i && i < i2 && r[i] != NO_ABS ==>
      i + 4 * numFields(r[i]) <= i2
   && (forall ii:int::{TV(ii)} TV(ii) ==> i < ii && ii < i + 4 * numFields(r[i]) ==> r[ii] == NO_ABS))
}

function ObjectSeq(i1:int, i2:int, r:[int]int) returns (bool)
{
    (i1 == i2 || r[i1] != NO_ABS)
 && (forall i:int::{TV(i)} TV(i) ==> i1 <= i && i < i2 && r[i] != NO_ABS ==>
        (forall ii:int::{TV(ii)} TV(ii) ==> i < ii && ii < i + 4 * numFields(r[i]) ==>
          r[ii] == NO_ABS)
     && (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields(r[i]) ==> gcAddr(i + 4 * j)) // REVIEW: necessary?
     && (   (i + 4 * numFields(r[i]) == i2)
         || (i + 4 * numFields(r[i]) < i2 && r[i + 4 * numFields(r[i])] != NO_ABS)))
}

function EmptySeq(i1:int, i2:int, r:[int]int, $toAbs:[int]int) returns (bool)
{
  (forall i:int::{TV(i)} TV(i) ==> i1 <= i && i < i2 ==> gcAddr(i) && r[i] == NO_ABS && $toAbs[i] == NO_ABS) // REVIEW: gcAddr necessary?
}

// invariant:
// note: typically, Tj = _tj and Tk = _tk
function CopyGcInv($freshAbs:int, BF:int, BT:int, HeapLo:int, Fi:int, Fk:int, Fl:int, Ti:int, Tj:int, _tj:int, Tk:int, _tk:int, Tl:int, $Time:Time, $r1:[int]int, $r2:[int]int,
  r1Live:bool, $toAbs:[int]int, $AbsMem:[int][int]int,
  $GcMem:[int]int, $gcSlice:[int]int) returns (bool)
{
    ?gcLo <= HeapLo
 && HeapLo <= ?gcHi
 && ((Fi == HeapLo && Ti == Fl && BF == ?gcLo) || (Ti == HeapLo && Fi == Tl && BT == ?gcLo))
 && (Fi == HeapLo ==> ?gcLo + BitIndex(HeapLo, Fl) == BT && ?gcLo + BitIndex(HeapLo, Tl) == HeapLo)
 && (Ti == HeapLo ==> ?gcLo + BitIndex(HeapLo, Tl) == BF && ?gcLo + BitIndex(HeapLo, Fl) == HeapLo)
 && Fi <= Fk && Fk <= Fl && Fl <= ?gcHi
 && Ti <= Tj && Tj <= _tj && _tj <= Tk && Tk <= _tk && _tk <= Tl && Tl <= ?gcHi
 && Aligned(Fi) && Aligned(Fk) && Aligned(Ti) && Aligned(Tj) && Aligned(Tk)
 && Aligned(?gcLo + BitIndex(HeapLo, Fi)) && Aligned(?gcLo + BitIndex(HeapLo, Ti))
 && ?gcLo <= ?gcLo + BitIndex(HeapLo, Fi) && ?gcLo + BitIndex(HeapLo, Fl) <= HeapLo
 && ?gcLo <= ?gcLo + BitIndex(HeapLo, Ti) && ?gcLo + BitIndex(HeapLo, Tl) <= HeapLo
 && BF == ?gcLo + BitIndex(HeapLo, Fi) && BT == ?gcLo + BitIndex(HeapLo, Ti)
 && (Fl - Fi) == Mult(32, (BitIndex(HeapLo, Fl) - BitIndex(HeapLo, Fi))) // Mult is faster than "*" here
 && (Tl - Ti) == Mult(32, (BitIndex(HeapLo, Tl) - BitIndex(HeapLo, Ti))) // Mult is faster than "*" here
 && bbvec4($r1, NO_ABS, Fi, $GcMem, Fi, Fi, Fl, ?gcLo + BitIndex(HeapLo, Fi), ?gcLo + BitIndex(HeapLo, Fl))
 && bbvec4($toAbs, NO_ABS, Ti, $GcMem, Ti, Ti, Tl, ?gcLo + BitIndex(HeapLo, Ti), ?gcLo + BitIndex(HeapLo, Tl))
 && WellFormed($toAbs)
 && ObjectSpc(Fi,  Fk, $r1)
 && EmptySeq( Fk,  Fl, $r1, $toAbs)
 && ObjectSpc(Ti,  Tj, $r2)
 && ObjectSeq(_tj, Tk, $r2)
 && EmptySeq( _tk, Tl, $r2, $toAbs)
 && (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $r1[i] != NO_ABS && r1Live ==> Fi <= i && i < Fk)
 && (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $r2[i] != NO_ABS ==> Ti <= i && i < _tk)
 && (forall i:int::{TV(i)} TV(i) ==> Fi <= i && i < Fk && $r1[i] != NO_ABS ==>
        ( IsFwdPtr($GcMem[i + 4]) <==> $toAbs[i] == NO_ABS)
     && ( IsFwdPtr($GcMem[i + 4])  ==> Pointer($r2, $GcMem[i + 4] - 4, $r1[i]) && AlignedHeapAddr(i + 4) && word($GcMem[i + 4]))
     && (!IsFwdPtr($GcMem[i + 4])  ==> $toAbs[i] == $r1[i])
     && (!IsFwdPtr($GcMem[i + 4])  ==> r1Live ==> ObjInv(i, $r1, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice))
     && i + 4 < Fk // REVIEW: hack?
     && Aligned(i) // REVIEW: redundant?
    )
 && (forall i:int::{TV(i)} TV(i) ==> Fi <= i && i < Fl && $toAbs[i] != NO_ABS ==> $r1[i] != NO_ABS && $r1[i] != NO_ABS)
 && (forall i:int::{TV(i)} TV(i) ==> Ti <= i && i < Tl && $toAbs[i] != NO_ABS ==> $r2[i] != NO_ABS && $r2[i] != NO_ABS)
 && (forall i:int::{TV(i)} TV(i) ==> Ti <= i && i < Tj && $r2[i] != NO_ABS ==>
        $toAbs[i] != NO_ABS && $toAbs[i] == $r2[i]
     && reached($toAbs[i], $Time)
     && ObjInv(i, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice)
     && !IsFwdPtr($GcMem[i + 4])
    )
 && (Tj != _tj ==> (forall j:int::{TO(j)} TO(j) ==> 0 <= j && Tj + 4 * j < _tj ==>
      gcAddr(Tj + 4 * j) && $gcSlice[Tj + 4 * j] == Tj)) // REVIEW: gcAddr necessary?
 && (forall i:int::{TV(i)} TV(i) ==> Tj < i && i < _tj ==> $r2[i] == NO_ABS)
 && (forall i:int::{TV(i)} TV(i) ==> _tj <= i && i < Tk && $r2[i] != NO_ABS ==>
        $toAbs[i] != NO_ABS && $toAbs[i] == $r2[i]
     && reached($toAbs[i], $Time)
     && ObjInv(i, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice)
     && !IsFwdPtr($GcMem[i + 4])
    )
 && (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $freshAbs && $r2[i] != $freshAbs)
}

function MutatorInv(BF:int, BT:int, HeapLo:int, Fi:int, Fk:int, Fl:int, Ti:int, Tj:int, Tk:int, Tl:int,
  $GcMem:[int]int, $toAbs:[int]int, $AbsMem:[int][int]int, $gcSlice:[int]int) returns (bool)
{
    ?gcLo <= HeapLo
 && HeapLo <= ?gcHi
 && ((Fi == HeapLo && Ti == Fl && BF == ?gcLo) || (Ti == HeapLo && Fi == Tl && BT == ?gcLo))
 && (Fi == HeapLo ==> ?gcLo + BitIndex(HeapLo, Fl) == BT && ?gcLo + BitIndex(HeapLo, Tl) == HeapLo)
 && (Ti == HeapLo ==> ?gcLo + BitIndex(HeapLo, Tl) == BF && ?gcLo + BitIndex(HeapLo, Fl) == HeapLo)
 && Fi <= Fk && Fk <= Fl && Fl <= ?gcHi
 && Ti <= Tj && Tj <= Tk && Tk <= Tl && Tl <= ?gcHi
 && Aligned(Fi) && Aligned(Fk) && Aligned(Ti) && Aligned(Tj) && Aligned(Tk)
 && Aligned(?gcLo + BitIndex(HeapLo, Fi)) && Aligned(?gcLo + BitIndex(HeapLo, Ti))
 && ?gcLo <= ?gcLo + BitIndex(HeapLo, Fi) && ?gcLo + BitIndex(HeapLo, Fl) <= HeapLo
 && ?gcLo <= ?gcLo + BitIndex(HeapLo, Ti) && ?gcLo + BitIndex(HeapLo, Tl) <= HeapLo
 && BF == ?gcLo + BitIndex(HeapLo, Fi) && BT == ?gcLo + BitIndex(HeapLo, Ti)
 && (Fl - Fi) == Mult(32, (BitIndex(HeapLo, Fl) - BitIndex(HeapLo, Fi))) // Mult is faster than "*" here
 && (Tl - Ti) == Mult(32, (BitIndex(HeapLo, Tl) - BitIndex(HeapLo, Ti))) // Mult is faster than "*" here
 && bbvec4($toAbs, NO_ABS, Fi, $GcMem, Fi, Fi, Fl, ?gcLo + BitIndex(HeapLo, Fi), ?gcLo + BitIndex(HeapLo, Fl))
 && WellFormed($toAbs)
 && ObjectSpc(Fi,  Fk, $toAbs)
 && EmptySeq( Fk,  Fl, $toAbs, $toAbs)
 && EmptySeq( Ti,  Tl, $toAbs, $toAbs)
 && (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> ($toAbs[i] != NO_ABS ==> Fi <= i && i < Fk))
 && (forall i:int::{TV(i)} TV(i) ==> Fi <= i && i < Fk && $toAbs[i] != NO_ABS ==>
        $toAbs[i] != NO_ABS
     && ObjInv(i, $toAbs, $toAbs, $toAbs, $AbsMem, $GcMem, $gcSlice)
     && !IsFwdPtr($GcMem[i + 4])
    )
 && (forall i:int::{TV(i)} TV(i) ==> Fi <= i && i < Fl && $toAbs[i] != NO_ABS ==> $toAbs[i] != NO_ABS)
 && (forall i:int::{TV(i)} TV(i) ==> Ti <= i && i < Tl && $toAbs[i] != NO_ABS ==> false)
}

procedure BB4Zero($a:[int]int, $on:int, $off:int, $aBase:int, $i0:int, $i1:int, $i2:int, $k:int, $g1:int, $g2:int, $_i0:int, $_g1:int)
  requires eax == $g1;
  requires ebx == $g2;
  requires (forall i:int::{TV(i)} TV(i) && $i1 <= i && i < $i2 ==> $a[$aBase + (i - $i0)] == $off);
  requires Aligned($g1) && Aligned($g2);
  requires $i2 - $i1 == 32 * ($g2 - $g1);
  requires word($i1 - $i0) && word($i2 - $i0);
  requires ?gcLo <= $g1 && $g1 <= $g2 && $g2 <= ?gcHi;
  requires $i1 == $i0;
  modifies $GcMem;
  modifies eax, ebx, esi, edi, ebp, esp;
  ensures  bbvec4($a, $off, $aBase, $GcMem, $i0, $i1, $i2, $g1, $g2);
  ensures  (forall i:int::{TV(i)} TV(i) && !between($g1, $g2, i) ==> $GcMem[i] == old($GcMem)[i]);
  ensures  (forall i:int::{TV(i)} TV(i) && !between($g1, $g2, i + 4) ==> $GcMem[i + 4] == old($GcMem)[i + 4]); // REVIEW: HACK?
  ensures  (forall i:int,j:int::{TV(i),TO(j)} TV(i) && TO(j) && !between($g1, $g2, i + 4 * j) ==> $GcMem[i + 4 * j] == old($GcMem)[i + 4 * j]); // REVIEW: HACK?
  ensures  (forall i:int::{TV(i)} TV(i) && !between($g1, $g2, $_g1 + BitIndex($_i0, i)) ==> $GcMem[$_g1 + BitIndex($_i0, i)] == old($GcMem)[$_g1 + BitIndex($_i0, i)]); // REVIEW: HACK?
{
  var $iter:int;
  esi := eax;
  $iter := $i1;
  //while (esi < $g2)
  loop:
    assert Aligned(esi) && TV(esi);
    assert $g1 <= esi && esi <= $g2;
    assert $iter - $i1 == 32 * (esi - $g1);
    assert bbvec4($a, $off, $aBase, $GcMem, $i0, $i1, $iter, $g1, $g2);
    assert (forall i:int::{TV(i)} TV(i) && !between($g1, $g2, i) ==> $GcMem[i] == old($GcMem)[i]);
    assert (forall i:int::{TV(i)} TV(i) && !between($g1, $g2, i + 4) ==> $GcMem[i + 4] == old($GcMem)[i + 4]); // REVIEW: HACK?
    assert (forall i:int,j:int::{TV(i),TO(j)} TV(i) && TO(j) && !between($g1, $g2, i + 4 * j) ==> $GcMem[i + 4 * j] == old($GcMem)[i + 4 * j]); // REVIEW: HACK?
    assert (forall i:int::{TV(i)} TV(i) && !between($g1, $g2, $_g1 + BitIndex($_i0, i)) ==> $GcMem[$_g1 + BitIndex($_i0, i)] == old($GcMem)[$_g1 + BitIndex($_i0, i)]); // REVIEW: HACK?
    if (esi >= ebx) { goto loopEnd; }

    call __notAligned(esi);
    call __bb4Zero($a, $off, $aBase, $GcMem, $i0, $i1, $iter, $g1, $g2, esi);
    call GcStore(esi, 0);//$GcMem[esi] := 0;
    $iter := $iter + 128;
    call esi := Add(esi, 4);
    assert TO(1);
    goto loop;
  loopEnd:

  assert esi == $g2;
  assert $iter == $i2;
  esp := esp + 4; return;
}

procedure bb4GetBit($a:[int]int, $off:int, $aBase:int, $i0:int, $i1:int, $i2:int, $k:int, $g1:int, $g2:int)
  requires bbvec4($a, $off, $aBase, $GcMem, $i0, $i1, $i2, $g1, $g2);
  requires word($k - $i0) && $i1 <= $k && $k < $i2;
  requires word($k) && word($i0) && Aligned($k) && Aligned($i0);
  requires word($i2 - $i0);
  requires eax == $g1;
  requires ebx == $k - $i0;
  requires Aligned($g1) && ?gcLo <= $g1 && $g2 <= ?gcHi;
  requires word($i1 - $i0) && word($i2 - $i0);
  modifies ebx, ecx, edx;
  ensures  ebx == 0 <==> $a[$aBase + ($k - $i0)] == $off;
{
  var $idx:int;
  var $bbb:int;
  $idx := $g1 + 4 * shr($k - $i0, 7);
  $bbb := and($GcMem[$idx], shl(1, and(shr($k - $i0, 2), 31)));
  call __subAligned($k, $i0);
  call __bb4GetBit($a, $off, $aBase, $GcMem, $i0, $i1, $i2, $k, $idx, $bbb, $g1, $g2);

  edx := ebx;
  assert TV($g1);
  assert TO(shr(ebx, 7));
  call ebx := Shr(ebx, 7);
  call edx := Shr(edx, 2);
  call ebx := Add(ebx, ebx);
  call ebx := Add(ebx, ebx);
  call ebx := Add(ebx, eax);
  call ebx := GcLoad(ebx);
  call edx := And(edx, 31);
  ecx := edx;
  edx := 1;
  call edx := Shl(edx, ecx);
  call ebx := And(ebx, edx);
}

procedure bb4SetBit($a:[int]int, $on:int, $off:int, $aBase:int, $i0:int, $i1:int, $i2:int, $k:int, $g1:int, $g2:int)
  requires bbvec4($a, $off, $aBase, $GcMem, $i0, $i1, $i2, $g1, $g2);
  requires word($k - $i0) && $i1 <= $k && $k < $i2;
  requires word($k) && word($i0) && Aligned($k) && Aligned($i0);
  requires $on != $off;
  requires word($i2 - $i0);
  requires esi == $k - $i0;
  requires edi == $g1;
  requires Aligned($g1) && ?gcLo <= $g1 && $g2 <= ?gcHi;
  requires word($i1 - $i0) && word($i2 - $i0);
  modifies esi, edi, ecx, $GcMem;
  ensures  bbvec4($a[$aBase + ($k - $i0) := $on], $off, $aBase, $GcMem, $i0, $i1, $i2, $g1, $g2);
  ensures  $GcMem == old($GcMem)[$g1 + BitIndex($i0, $k) := edi];
  ensures  Aligned($k - $i0);
{
  var $idx:int;
  var $bbb:int;
  $idx := $g1 + 4 * shr($k - $i0, 7);
  $bbb := or($GcMem[$idx], shl(1, and(shr($k - $i0, 2), 31)));
  call __subAligned($k, $i0);
  call __bb4SetBit($a, $on, $off, $aBase, $GcMem, $i0, $i1, $i2, $k, $idx, $bbb, $GcMem[$idx := $bbb], $g1, $g2);

  ecx := esi;
  assert TV($g1);
  assert TO(shr(esi, 7));
  call esi := Shr(esi, 7);
  call ecx := Shr(ecx, 2);
  call esi := Add(esi, esi);
  call esi := Add(esi, esi);
  call esi := Add(esi, edi);
  call ecx := And(ecx, 31);
  edi := 1;
  call edi := Shl(edi, ecx);
  ecx := edi; // REVIEW: optimize this more
  call edi := GcLoad(esi);
  call edi := Or(edi, ecx);
  call GcStore(esi, edi);
}

procedure copyWord($ptr:int, $_tj:int, $ret:int, $ind:int, $s:int)
  requires ecx == $ptr && esi == $ret && edi == $ind;
  requires Pointer($r1, $ptr, $r1[$ptr]) && TV($ptr);
  requires !IsFwdPtr($GcMem[$ptr + 4]);
  requires $_tj <= Tk;

  requires $s == 4 * numFields($r1[$ptr]);
  requires Tk == $ret + $s;
  requires Tk <= Tl;

  requires TO($ind) && 0 <= $ind && $ind < numFields($r1[$ptr]);
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, $_tj, $ret, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> gcAddr($ret + 4 * j) && $gcSlice[$ret + 4 * j] == $ret); // REVIEW: gcAddr necessary?
  requires EmptySeq($ret + 4 * $ind, Tk, $r2, $toAbs);
  requires (forall j:int::{TO(j)} TO(j) ==>
              0 <= j && j < $ind ==> Value(VFieldPtr($r1[$ptr], j), $r1, $GcMem[$ret + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
  requires (forall i:int::{TV(i)} TV(i) ==> $ret < i && i < $ret + 4 * $ind ==> $r2[i] == NO_ABS);
  requires $r2[$ret] == NO_ABS;

  modifies $GcMem, $gcSlice;
  modifies eax, ebx;

  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, $_tj, $ret, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind + 1 ==> gcAddr($ret + 4 * j) && $gcSlice[$ret + 4 * j] == $ret); // REVIEW: gcAddr necessary?
  ensures  (forall j:int::{TO(j)} TO(j) ==>
              0 <= j && j < $ind + 1 ==> Value(VFieldPtr($r1[$ptr], j), $r1, $GcMem[$ret + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && Tj + 4 * j < $_tj ==>
              $GcMem[Tj + 4 * j] == old($GcMem)[Tj + 4 * j] && $gcSlice[Tj + 4 * j] == old($gcSlice[Tj + 4 * j]));

  ensures RExtend(old($r2), $r2);
{
  assert TO(numFields($r1[$ptr]));
  assert TV($ret);

  call eax := GcLoad(ecx + 4 * edi);
  assert TV($ret + 4 * $ind);
  $gcSlice[$ret + 4 * $ind] := $ret;
  call GcStore(esi + 4 * edi, eax);
  assert TO(1);
}

procedure CopyAndForward($ptr:int, $_tj:int)
  requires ecx == $ptr;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, $_tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Pointer($r1, $ptr, $r1[$ptr]) && TV($ptr);
  requires !IsFwdPtr($GcMem[$ptr + 4]);
  requires $_tj <= Tk;
  requires reached($toAbs[$ptr], $Time);
  modifies $r2, $GcMem, $toAbs, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, $_tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
  ensures  Pointer($r2, eax, $r1[$ptr]);
  ensures  Tj == old(Tj);
  ensures  Tk >= old(Tk);
  ensures  old($toAbs)[Tj] != NO_ABS ==> $toAbs[Tj] != NO_ABS && $toAbs[Tj] == old($toAbs)[Tj];
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && Tj + 4 * j < $_tj ==>
              $GcMem[Tj + 4 * j] == old($GcMem)[Tj + 4 * j] && $gcSlice[Tj + 4 * j] == old($gcSlice[Tj + 4 * j]));
  ensures  Ti <= eax && eax < Tk && gcAddrEx(eax + 4);
{
  var tmp:int;

  call edx := GcLoad(ecx + 4);
  esp := esp - 4; call GetSize($ptr, edx, $r1, $r1);
  ebp := eax;
  assert TO(numFields($r1[$ptr]));

  esi := Tk;
  call Tk := AddChecked(Tk, ebp);
  assert TV(esi);

  eax := Tl;
  if (Tk <= eax) { goto skip1; }
    // out of memory
    call DebugBreak();
  skip1:

  edi := 0;
  edx := 0;
  // while (edx < ebp)
  loop:
    assert 4 * edi == edx;
    assert TO(edi) && 0 <= edi && edi <= numFields($r1[$ptr]);
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, $_tj, esi, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < edi ==> gcAddr(esi + 4 * j) && $gcSlice[esi + 4 * j] == esi); // REVIEW: gcAddr necessary?
    assert EmptySeq(esi + 4 * edi, Tk, $r2, $toAbs);
    assert (forall j:int::{TO(j)} TO(j) ==>
                0 <= j && j < edi ==> Value(VFieldPtr($r1[$ptr], j), $r1, $GcMem[esi + 4 * j], $AbsMem[$toAbs[$ptr]][j]));
    assert (forall i:int::{TV(i)} TV(i) ==> esi < i && i < esi + 4 * edi ==> $r2[i] == NO_ABS);
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && Tj + 4 * j < $_tj ==>
                $GcMem[Tj + 4 * j] == old($GcMem)[Tj + 4 * j] && $gcSlice[Tj + 4 * j] == old($gcSlice[Tj + 4 * j]));
    assert $r2[esi] == NO_ABS;
    if (edx >= ebp) { goto loopEnd; }

    call copyWord($ptr, $_tj, esi, edi, ebp);
    call edi := Add(edi, 1);
    call edx := Add(edx, 4);
    goto loop;
  loopEnd:

  call eax := Lea(esi + 4);
  call GcStore(ecx + 4, eax);

  eax := esi;

  call esi := Sub(esi, Ti);

  edi := BT;
  call bb4SetBit($toAbs, $r1[$ptr], NO_ABS, Ti, Ti, Ti, Tl, eax, ?gcLo + BitIndex(HeapLo, Ti), ?gcLo + BitIndex(HeapLo, Tl));

  $r2[eax] := $r1[$ptr];
  $toAbs[eax] := $toAbs[$ptr];
  $toAbs[$ptr] := NO_ABS;
  assert TO(1);

  assert TV(eax - Ti);

  esp := esp + 4; return;
}

procedure forwardFromspacePtr($ptr:int, $abs:int, $_tj:int)
  requires ecx == $ptr;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, $_tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires word($ptr);
  requires Pointer($r1, $ptr - 4, $abs);
  requires $_tj <= Tk;
  requires IsFwdPtr($GcMem[$ptr]) || reached($toAbs[$ptr - 4], $Time);
  modifies $r2, $GcMem, $toAbs, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, $_tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
  ensures  Pointer($r2, eax - 4, $abs);
  ensures  Tj == old(Tj);
  ensures  Tk >= old(Tk);
  ensures  old($toAbs)[Tj] != NO_ABS ==> $toAbs[Tj] != NO_ABS && $toAbs[Tj] == old($toAbs)[Tj];
  ensures  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && Tj + 4 * j < $_tj ==>
              $GcMem[Tj + 4 * j] == old($GcMem)[Tj + 4 * j] && $gcSlice[Tj + 4 * j] == old($gcSlice[Tj + 4 * j]));
  ensures  Ti <= eax - 4 && eax - 4 < Tk;
  ensures  gcAddrEx(eax);
{
  assert TV($ptr - 4);
  call eax := GcLoad(ecx);

  if (?gcLo > eax) { goto skip; }
  if (?gcHi >= eax) { goto done; }
  skip:
    call ecx := Sub(ecx, 4);
    esp := esp - 4; call CopyAndForward($ptr - 4, $_tj);
    call eax := Add(eax, 4);
  done:
  assert TV(eax - 4);
}

procedure scanObjectDense($vt:int)
  requires ecx == $vt;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires tag($vt) == ?DENSE_TAG;
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  var save1:int;
  var save2:int;
  var save3:int;
  assert TO(numFields($r2[Tj]));

  esi := 2;
  assert TVT($r2[Tj], $vt);
  assert TVL($r2[Tj]);
  call ebp := RoLoad32(ecx + ?VT_BASE_LENGTH);
  call edx := RoLoad32(ecx + ?VT_MASK);
  edi := Tj;
  call edi := Add(edi, 8);
  call ebp := Add(ebp, Tj);

  //while (edi < ebp)
  loop:
    assert TO(esi);// && 0 < esi;
    assert edi == Tj + 4 * esi && ebp == Tj + 4 * numFields($r2[Tj]) && edx == mask($vt);
    assert 2 <= esi && esi <= numFields($r2[Tj]);
    assert Pointer($r2, Tj, $r2[Tj]);
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj + 4 * numFields($r2[Tj]), Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial(Tj, 0, esi, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial(Tj, esi, numFields($r2[Tj]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[Tj] != NO_ABS && $toAbs[Tj] == $r2[Tj];
    if (edi >= ebp) { goto loopEnd; }
    if (esi >= 30) { goto loopEnd; }

    assert TO(0) && TO(1);
    assert TVT($r2[Tj], $vt);
    assert TVL($r2[Tj]);
    //assert getBit(mask($vt), 2 + esi) == VFieldPtr($r2[Tj], esi);
    //if (getBit(mask, 2 + esi))
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
        call reach($toAbs[Tj], esi, $Time);

        save1 := esi;
        save2 := ebp;
        save3 := edx;
        call forwardFromspacePtr(ecx, $AbsMem[$toAbs[Tj]][esi], Tj + 4 * numFields($r2[Tj]));
        esi := save1;
        ebp := save2;
        edx := save3;
        edi := Tj;
        call edi := Lea(edi + 4 * esi);

        call GcStore(edi, eax);
      skip2:
    skip1:

    call esi := Add(esi, 1);
    call edi := Add(edi, 4);
    goto loop;
  loopEnd:

  assert TVT($r2[Tj], $vt);
  assert TVL($r2[Tj]);
  Tj := ebp;
  assert TO(1);
}

procedure scanObjectSparse($vt:int)
  requires ecx == $vt;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires tag($vt) == ?SPARSE_TAG;
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  var save1:int;
  var save2:int;
  var save3:int;
  var save4:int;
  assert TO(numFields($r2[Tj]));

  esi := 1;

  assert TO(numFields($r2[Tj]));
  assert TVT($toAbs[Tj], $vt);
  call ebp := RoLoad32(ecx + ?VT_BASE_LENGTH);
  call edx := RoLoad32(ecx + ?VT_MASK);
  assert TVL($r2[Tj]);

  esi := 1;
  //while (esi < 8)
  loop:
    assert edx == mask($vt) && ebp == 4 * numFields($r2[Tj]);
    assert TSlot(esi) && 0 < esi && esi <= 8;
    assert Pointer($r2, Tj, $r2[Tj]);
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj + 4 * numFields($r2[Tj]), Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    assert ObjInvBase(Tj, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($r2[Tj]) ==>
                between(1, esi, fieldToSlot($vt, j - 2)) ==>
                  ObjInvField(Tj, j, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($r2[Tj]) ==>
                !between(1, esi, fieldToSlot($vt, j - 2)) ==>
                  ObjInvField(Tj, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert $toAbs[Tj] != NO_ABS && $toAbs[Tj] == $r2[Tj];
    if (esi >= 8) { goto loopEnd; }

    assert TO(0) && TO(1);
    assert TVT($toAbs[Tj], $vt);
    assert TO(getNib(edx, 4 * esi) + 1);

    //if (getNib(edx, 4 * esi) != 0)
    ecx := 0;
    call ecx := Lea(ecx + 4 * esi);
    ebx := edx;
    call ebx := Shr(ebx, ecx);
    call ebx := And(ebx, 15);
    if (ebx == 0) { goto skip1; }
      eax := Tj;
      call ecx := GcLoad(eax + 4 * ebx + 4);

      //if (gcAddrEx(ecx))
      if (ecx < ?gcLo) { goto skip2; }
      if (ecx > ?gcHi) { goto skip2; }
        assert TV(ecx - 4);
        call reach($toAbs[Tj], 1 + ebx, $Time);

        save1 := esi;
        save2 := ebp;
        save3 := edx;
        save4 := ebx;
        call forwardFromspacePtr(ecx, $AbsMem[$toAbs[Tj]][1 + getNib(edx, 4 * esi)], Tj + ebp);
        esi := save1;
        ebp := save2;
        edx := save3;
        ebx := save4;

        ecx := Tj;
        call GcStore(ecx + 4 * ebx + 4, eax);
      skip2:
    skip1:

    call esi := Add(esi, 1);
    goto loop;
  loopEnd:

  assert TVT($toAbs[Tj], $vt);
  assert TVL($r2[Tj]);
  call Tj := Add(Tj, ebp);
  assert TO(1);
}

procedure scanObjectOtherVectorNoPointers($vt:int)
  requires ecx == $vt;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires tag($vt) == ?OTHER_VECTOR_TAG;
  requires arrayOf($vt) != ?TYPE_STRUCT || (arrayOf($vt) == ?TYPE_STRUCT && mask(arrayElementClass($vt)) == ?SPARSE_TAG);
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  edx := ecx;
  ecx := Tj;
  esp := esp - 4; call GetSize(Tj, $vt, $r2, $r1);

  assert TO(numFields($r2[Tj]));
  assert TVT($r2[Tj], $vt);
  call Tj := Add(Tj, eax);
}

procedure scanObjectOtherVectorPointersSparseFields($vt:int, $jj:int, $index:int)
  requires edx == mask(arrayElementClass($vt));
  requires edi == $jj;
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires tag($vt) == ?OTHER_VECTOR_TAG;
  requires arrayOf($vt) == ?TYPE_STRUCT && tag(arrayElementClass($vt)) == ?SPARSE_TAG;
  requires TO($jj) && $jj == baseWords($vt) + Mult(arrayElementWords($vt), $index);
  requires $jj < numFields($r2[Tj]);
  requires TO($index) && 0 <= $index; // && $index <= nElems;
  requires Mult(arrayElementWords($vt), $index) >= 0;
  requires reached($toAbs[Tj], $Time);
  requires Pointer($r2, Tj, $r2[Tj]);
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj + 4 * numFields($r2[Tj]), Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires ObjInvPartial(Tj, 0, $jj, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires ObjInvPartial(Tj, $jj, numFields($r2[Tj]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires $toAbs[Tj] != NO_ABS && $toAbs[Tj] == $r2[Tj];
  requires (forall j:int::{TO(j)} TO(j) ==>
             between(0, arrayElementWords($vt), j - $jj) ==>
               ObjInvField(Tj, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));

  modifies $r2, $GcMem, $toAbs, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  Pointer($r2, Tj, $r2[Tj]);
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj + 4 * numFields($r2[Tj]), Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
  ensures  ObjInvPartial(Tj, 0, $jj, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  ObjInvPartial(Tj, $jj + arrayElementWords($vt), numFields($r2[Tj]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  $toAbs[Tj] != NO_ABS && $toAbs[Tj] == $r2[Tj];
  ensures  (forall j:int::{TO(j)} TO(j) ==>
             between(0, arrayElementWords($vt), j - $jj) ==>
               between(1, 8, fieldToSlot(arrayElementClass($vt), j - $jj)) ==>
                 ObjInvField(Tj, j, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
  ensures  (forall j:int::{TO(j)} TO(j) ==>
             between(0, arrayElementWords($vt), j - $jj) ==>
               !between(1, 8, fieldToSlot(arrayElementClass($vt), j - $jj)) ==>
                 ObjInvField(Tj, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));
  ensures  edi == old(edi);
  ensures  edx == old(edx);
{
  var save1:int;
  var save2:int;
  var save3:int;
  var save4:int;

  assert TO(numFields($r2[Tj]));
  assert TO(2);
  assert TVT($r2[Tj], $vt);
  assert TVL($r2[Tj]);

  esi := 1;
  //while (esi < 8)
  loop:
    assert TSlot(esi) && 0 < esi && esi <= 8;
    assert edx == mask(arrayElementClass($vt));
    assert edi == $jj;
    assert Pointer($r2, Tj, $r2[Tj]);
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj + 4 * numFields($r2[Tj]), Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial(Tj, 0, $jj, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial(Tj, $jj + arrayElementWords($vt), numFields($r2[Tj]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[Tj] != NO_ABS && $toAbs[Tj] == $r2[Tj];
    assert (forall j:int::{TO(j)} TO(j) ==>
                between(0, arrayElementWords($vt), j - $jj) ==>
                  between(1, esi, fieldToSlot(arrayElementClass($vt), j - $jj)) ==>
                    ObjInvField(Tj, j, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert (forall j:int::{TO(j)} TO(j) ==>
                between(0, arrayElementWords($vt), j - $jj) ==>
                  !between(1, esi, fieldToSlot(arrayElementClass($vt), j - $jj)) ==>
                    ObjInvField(Tj, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));
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

      eax := Tj;
      call ecx := GcLoad(eax + 4 * ebx);
      //if (gcAddrEx(ecx))
      if (ecx < ?gcLo) { goto skip2; }
      if (ecx > ?gcHi) { goto skip2; }

        assert TV(ecx - 4);
        call reach($toAbs[Tj], ebx, $Time);

        assert TO(0);
        assert TO(1);

        save1 := esi;
        save2 := edi;
        save3 := edx;
        save4 := ebx;
        call forwardFromspacePtr(ecx, $AbsMem[$toAbs[Tj]][ebx], Tj + 4 * numFields($r2[Tj]));
        esi := save1;
        edi := save2;
        edx := save3;
        ebx := save4;

        ecx := Tj;
        call GcStore(ecx + 4 * ebx, eax);

      skip2:
    skip1:
    call esi := Add(esi, 1);
    goto loop;
  loopEnd:
}

procedure scanObjectOtherVectorPointers($vt:int)
  requires ecx == $vt;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires tag($vt) == ?OTHER_VECTOR_TAG;
  requires arrayOf($vt) == ?TYPE_STRUCT && tag(arrayElementClass($vt)) == ?SPARSE_TAG;
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  var save1:int;
  var save2:int;

  var $index:int;

  assert TO(numFields($r2[Tj]));
  assert TO(2);
  assert TVT($r2[Tj], $vt);
  assert TVL($r2[Tj]);

  $index := 0;

  call edi := RoLoad32(ecx + ?VT_BASE_LENGTH);
  call ebx := RoLoad32(ecx + ?VT_ARRAY_ELEMENT_SIZE);
  edx := Tj;
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

    assert ebp == 4 * numFields($r2[Tj]);
    assert edx == mask(arrayElementClass($vt));
    assert ebx == arrayElementWords($vt);
    assert 4 * edi <= ebp;

    assert Pointer($r2, Tj, $r2[Tj]);
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj + 4 * numFields($r2[Tj]), Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial(Tj, 0, edi, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial(Tj, edi, numFields($r2[Tj]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[Tj] != NO_ABS && $toAbs[Tj] == $r2[Tj];
    eax := 0;
    call eax := Lea(eax + 4 * edi);
    if (eax >= ebp) { goto loopEnd; }

    save1 := ebx;
    save2 := ebp;
    call scanObjectOtherVectorPointersSparseFields($vt, edi, $index);
    ebx := save1;
    ebp := save2;

    assert TVM3(ebx, $index, 1);
    assert TVM(ebx, $index);
    $index := $index + 1;
    call edi := Add(edi, ebx);
    goto loop;
  loopEnd:

  call Tj := Add(Tj, ebp);
  assert TO(1);
}

procedure scanObjectPtrArray($vt:int)
  requires ecx == $vt;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires tag($vt) == ?PTR_ARRAY_TAG;
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  var $ind:int;
  var save1:int;
  var save2:int;

  assert TO(numFields($r2[Tj]));
  assert TO(3);
  assert TVT($r2[Tj], $vt);
  assert TVL($r2[Tj]);

  ebx := Tj;
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
    assert edi == Tj + 4 * $ind;
    assert ebp == Tj + 4 * numFields($r2[Tj]);
    assert TO($ind) && baseWords($vt) <= $ind; // && $ind <= nElems + 3;
    assert Pointer($r2, Tj, $r2[Tj]);
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj + 4 * numFields($r2[Tj]), Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial(Tj, 0, $ind, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial(Tj, $ind, numFields($r2[Tj]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[Tj] != NO_ABS && $toAbs[Tj] == $r2[Tj];
    if (edi >= ebp) { goto loopEnd; }

    assert TO(0) && TO(1) && TO(3);
    assert TVT($r2[Tj], $vt);
    assert TVL($r2[Tj]);
    call ecx := GcLoad(edi);
    //if (gcAddrEx(ecx))
    if (ecx < ?gcLo) { goto skip1; }
    if (ecx > ?gcHi) { goto skip1; }
      assert TV(ecx - 4);
      call reach($toAbs[Tj], $ind, $Time);

      save1 := edi;
      save2 := ebp;
      call forwardFromspacePtr(ecx, $AbsMem[$toAbs[Tj]][$ind], ebp);
      edi := save1;
      ebp := save2;

      call GcStore(edi, eax);
    skip1:

    $ind := $ind + 1;
    call edi := Add(edi, 4);
    goto loop;
  loopEnd:

  Tj := ebp;
}

procedure scanObjectPtrVector($vt:int)
  requires ecx == $vt;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires tag($vt) == ?PTR_VECTOR_TAG;
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  var $ind:int;
  var save1:int;
  var save2:int;
  assert TO(numFields($r2[Tj]));
  assert TO(2);
  assert TVT($r2[Tj], $vt);
  assert TVL($r2[Tj]);

  ebx := Tj;
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
    assert edi == Tj + 4 * $ind;
    assert ebp == Tj + 4 * numFields($r2[Tj]);
    assert TO($ind) && baseWords($vt) <= $ind; // && $ind <= nElems + 3;
    assert Pointer($r2, Tj, $r2[Tj]);
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj + 4 * numFields($r2[Tj]), Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    assert ObjInvPartial(Tj, 0, $ind, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert ObjInvPartial(Tj, $ind, numFields($r2[Tj]), $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert $toAbs[Tj] != NO_ABS && $toAbs[Tj] == $r2[Tj];
    if (edi >= ebp) { goto loopEnd; }

    assert TO(0) && TO(1) && TO(2);
    assert TVT($r2[Tj], $vt);
    call ecx := GcLoad(edi);
    //if (gcAddrEx(ecx))
    if (ecx < ?gcLo) { goto skip1; }
    if (ecx > ?gcHi) { goto skip1; }
      assert TV(ecx - 4);
      call reach($toAbs[Tj], $ind, $Time);

      save1 := edi;
      save2 := ebp;
      call forwardFromspacePtr(ecx, $AbsMem[$toAbs[Tj]][$ind], ebp);
      edi := save1;
      ebp := save2;

      call GcStore(edi, eax);
    skip1:

    $ind := $ind + 1;
    call edi := Add(edi, 4);
    goto loop;
  loopEnd:

  Tj := ebp;
}

procedure scanObjectOtherArrayNoPointers($vt:int)
  requires ecx == $vt;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires tag($vt) == ?OTHER_ARRAY_TAG;
  requires arrayOf($vt) != ?TYPE_STRUCT;
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  edx := ecx;
  ecx := Tj;
  esp := esp - 4; call GetSize(Tj, $vt, $r2, $r1);

  assert TO(numFields($r2[Tj]));
  assert TVT($r2[Tj], $vt);
  call Tj := Add(Tj, eax);
}

procedure scanObjectString($vt:int)
  requires ecx == $vt;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires tag($vt) == ?STRING_TAG;
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  edx := ecx;
  ecx := Tj;
  esp := esp - 4; call GetSize(Tj, $vt, $r2, $r1);

  assert TO(numFields($r2[Tj]));
  assert TVT($r2[Tj], $vt);
  call Tj := Add(Tj, eax);
}

procedure scanObjectOther($vt:int)
  requires ecx == $vt;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  requires $vt == $AbsMem[$r2[Tj]][1];
  requires isOtherTag(tag($vt));
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  var save1:int;
  var save2:int;
  var save3:int;
  var save4:int;
  var save5:int;

  assert TO(numFields($r2[Tj]));
  assert TVT($toAbs[Tj], $vt);
  assert TVL($r2[Tj]);

  call edx := RoLoad32(ecx + ?VT_MASK);
  call edi := RoLoad32(edx);
  call ebp := RoLoad32(ecx + ?VT_BASE_LENGTH);

  esi := 1;

  //while (esi < edi + 1)
  loop:
    assert ebp == 4 * numFields($r2[Tj]);
    assert edx == mask($vt);
    assert edi == ro32(mask($vt));
    assert TSlot(esi) && 0 < esi && esi <= ro32(mask($vt)) + 1;
    assert Pointer($r2, Tj, $r2[Tj]);
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj + 4 * numFields($r2[Tj]), Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    assert ObjInvBase(Tj, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($r2[Tj]) ==>
                between(1, esi, fieldToSlot($vt, j)) ==>
                  ObjInvField(Tj, j, $r2, $r2, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < numFields($r2[Tj]) ==>
                !between(1, esi, fieldToSlot($vt, j)) ==>
                  ObjInvField(Tj, j, $r2, $r1, $toAbs, $AbsMem, $GcMem, $gcSlice));
    assert $toAbs[Tj] != NO_ABS && $toAbs[Tj] == $r2[Tj];
    if (esi > edi) { goto loopEnd; }

    assert TO(0) && TO(1);
    assert TVT($toAbs[Tj], $vt);
    assert TVL($r2[Tj]);
    assert TO(ro32(mask($vt) + 4 * esi) + 1);
    call ebx := RoLoad32(edx + 4 * esi);
    //if (ebx != 0)
    if (ebx == 0) { goto skip1; }
      eax := Tj;
      call ecx := GcLoad(eax + 4 * ebx + 4);

      //if (gcAddrEx(ecx))
      if (ecx < ?gcLo) { goto skip2; }
      if (ecx > ?gcHi) { goto skip2; }
        assert TV(ecx - 4);
        call reach($toAbs[Tj], 1 + ro32(edx + 4 * esi), $Time);

        save1 := ebx;
        save2 := esi;
        save3 := edi;
        save4 := ebp;
        save5 := edx;
        call forwardFromspacePtr(ecx, $AbsMem[$toAbs[Tj]][1 + ro32(edx + 4 * esi)], Tj + ebp);
        ebx := save1;
        esi := save2;
        edi := save3;
        ebp := save4;
        edx := save5;

        ecx := Tj;
        call GcStore(ecx + 4 * ebx + 4, eax);
      skip2:
    skip1:
    call esi := AddChecked(esi, 1);
    goto loop;
  loopEnd:

  assert TVT($toAbs[Tj], $vt);
  assert TVL($r2[Tj]);
  call Tj := Add(Tj, ebp);
}

procedure scanObject()
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires Tj < Tk;
  requires TV(Tj);
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
{
  var $vt:int;

  assert TO(1);
  ecx := Tj;
  call ecx := GcLoad(ecx + 4);
  $vt := ecx;

  assert TO(numFields($r2[Tj]));

  call readTag($toAbs[Tj], $vt);

  if (eax != ?SPARSE_TAG) { goto skip1; }
    call scanObjectSparse($vt);
    goto end;
  skip1:

  if (eax != ?DENSE_TAG) { goto skip2; }
    call scanObjectDense($vt);
    goto end;
  skip2:

  if (eax != ?STRING_TAG) { goto skip3; }
    call scanObjectString($vt);
    goto end;
  skip3:

  if (eax != ?PTR_VECTOR_TAG) { goto skip4; }
    call scanObjectPtrVector($vt);
    goto end;
  skip4:

  if (eax != ?OTHER_VECTOR_TAG) { goto skip5; }
    call readArrayOf($r2[Tj], $vt);
    call readElementInfo($r2[Tj], $vt);
    if (ebp != ?TYPE_STRUCT) { goto noPoint; }
    if (ebp != ?TYPE_STRUCT) { goto vecSkip1; }
    if (edi != ?SPARSE_TAG) { goto vecSkip1; }
    noPoint:
      call scanObjectOtherVectorNoPointers($vt);
      goto end;
    vecSkip1:
    if (ebp != ?TYPE_STRUCT) { goto vecSkip2; }

    //if (tag(arrayElementClass(vt)) != ?SPARSE_TAG) { goto vecSkip2; }
    eax := edi;
    call eax := And(eax, 15);
    if (eax != ?SPARSE_TAG) { goto vecSkip2; }

      call scanObjectOtherVectorPointers($vt);
      goto end;

    vecSkip2:
      assert !(
          (ebp != ?TYPE_STRUCT)
       || (ebp == ?TYPE_STRUCT && edi == ?SPARSE_TAG)
       || (ebp == ?TYPE_STRUCT && tag(arrayElementClass($vt)) == ?SPARSE_TAG));
      call DebugBreak();

  skip5:

  if (eax != ?PTR_ARRAY_TAG) { goto skip6; }
    call scanObjectPtrArray($vt);
    goto end;
  skip6:

  if (eax != ?OTHER_ARRAY_TAG) { goto skip7; }
    call readArrayOf($r2[Tj], $vt);
    if (ebp == ?TYPE_STRUCT) { goto arraySkip1; }
      call scanObjectOtherArrayNoPointers($vt);
      goto end;
    arraySkip1:
      call DebugBreak();
    goto end;
  skip7:

    call scanObjectOther($vt);

  end:
}

procedure scanObjects()
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  modifies $r2, $GcMem, $toAbs, Tj, Tk, $gcSlice;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
  ensures  Tj == Tk;
{
  entry:
  loop:
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    eax := Tk;
    if (Tj >= eax) { goto exit; }
    call scanObject();
    goto loop;
  exit:
}

procedure FromInteriorPointer($iptr:int, $offset:int, $abs:int)
  requires ecx == $iptr;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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
    call ebx := Sub(ebx, Fi);
    edx := ebx;
    call edx := And(edx, 3);
    call __andAligned(ebx);
    call __addAligned(Fi, ebx);
    if (edx != 0)
    {
      goto skip1;
    }

    save1 := eax;
    save2 := ecx;
    eax := BF;
    call bb4GetBit($r1, NO_ABS, Fi, Fi, Fi, Fl, $iptr - save1 - 4, ?gcLo + BitIndex(HeapLo, Fi), ?gcLo + BitIndex(HeapLo, Fl));
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

procedure scanStackWordDenseCopy($frame:int, $addr:int, $desc:int, $addrp:int, $p:int, $args:int)
  requires ecx == $addrp;
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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

  modifies $r2, $GcMem, $toAbs, Tk, $gcSlice, $FrameMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
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

  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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

    call forwardFromspacePtr(ecx, $FrameAbs[$frame][$p], Tj);

    assert TV(eax - 4);
    call eax := Add(eax, offset);
    call scanStackUpdateInvs($r1, 0, $frame, $frame, $addrp, eax);
    call scanStackUpdateInvs($r2, $frame + 1, $FrameCount, $frame, $addrp, eax);

    ecx := save1;
    call FrameStore(($frame), ecx, eax);
  skip1:
}

procedure scanStackDenseCopy($frame:int, $addr:int, $desc:int)
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
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  modifies $r2, $GcMem, $toAbs, Tk, $gcSlice, $FrameMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f <= $frame - 1 ==>
    FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures (forall f:int::{TV(f)} TV(f) ==> $frame - 1 < f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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

    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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
      call scanStackWordDenseCopy($frame, $addr, $desc, $addr + 4 * (args + 1 - b), args + 1 - b, args);
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

    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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
      call scanStackWordDenseCopy($frame, $addr, $desc, $addr + 4 * (args - 1 - b), args - 1 - b, args);
    skip2:
    call b := Add(b, 1);
    call addrp := SubChecked(addrp, 4);
    goto loop2;
  loopEnd2:
}

procedure scanStackSparse8Copy($frame:int, $addr:int, $desc:int)
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
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  modifies $r2, $GcMem, $toAbs, Tk, $gcSlice, $FrameMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f <= $frame - 1 ==>
    FrameInv(f, $FrameLayout[f], $r1, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures (forall f:int::{TV(f)} TV(f) ==> $frame - 1 < f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $r2, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, $Time));
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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

    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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
      call forwardFromspacePtr(ecx, $FrameAbs[$frame][roS8(desc + 6 + p)], Tj);
      assert TV(eax - 4);
      call eax := Add(eax, offset);
      call scanStackUpdateInvs($r1, 0, $frame, $frame, addr + 4 * roS8(desc + 6 + p), eax);
      call scanStackUpdateInvs($r2, $frame + 1, $FrameCount, $frame, addr + 4 * roS8(desc + 6 + p), eax);
      ebx := addrp;
      call FrameStore(($frame), ebx, eax);
    skip1:

    // This is just here to improve performance:
    assert (forall j:int::{TO(j)} TO(j) ==> inFrame($FrameLayout[$frame], j) &&
      p == frameFieldToSlot($FrameLayout[$frame], j) ==> j == roS8(desc + 6 + p));

    call p := Add(p, 1);
    goto loop;
  loopEnd:
}

procedure scanStackCopy($ra:int, $nextFp:int)
  requires ecx == $ra && word($ra);
  requires edx == $nextFp;
  requires FrameNextInv($FrameCount, $ra, $nextFp, $FrameAddr, $FrameLayout);
  requires StackInv($r1, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  modifies $r2, $GcMem, $toAbs, Tk, $gcSlice, $FrameMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  StackInv($r2, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  ensures  RExtend(old($r2), $r2);
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
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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
      call scanStackDenseCopy($frame, addr, desc);
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
      call scanStackSparse8Copy($frame, addr, desc);
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

procedure scanStaticSectionCopy($section:int)
  requires ecx == $section;
  requires 0 <= $section && $section < ?sectionCount && TV($section);
  requires (forall s:int::{TV(s)} TV(s) ==> $section <= s && s < ?sectionCount ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), $r1, $SectionMem, $SectionAbs, $Time));
  requires (forall s:int::{TV(s)} TV(s) ==> 0 <= s && s < $section ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), $r2, $SectionMem, $SectionAbs, $Time));
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  modifies $r2, $GcMem, $toAbs, Tk, $gcSlice, $SectionMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  (forall s:int::{TV(s)} TV(s) ==> $section + 1 <= s && s < ?sectionCount ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), $r1, $SectionMem, $SectionAbs, $Time));
  ensures  (forall s:int::{TV(s)} TV(s) ==> 0 <= s && s < $section + 1 ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), $r2, $SectionMem, $SectionAbs, $Time));
  ensures  CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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

    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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
        call forwardFromspacePtr(ecx, $SectionAbs[section][esi], Tj);
        edi := save1;
        esi := save2;
        edx := save3;

        call SectionStore(edi, eax);
      skip2:
    skip1:

    call esi := Add(esi, 1);
    call edi := AddChecked(edi, 4);
    goto loop;
  loopEnd:
}

procedure scanStaticCopy()
  requires StaticInv($r1, $SectionMem, $SectionAbs, $Time);
  requires CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
  modifies $r2, $GcMem, $toAbs, Tk, $gcSlice, $SectionMem;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures  StaticInv($r2, $SectionMem, $SectionAbs, $Time);
  ensures CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
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
    assert CopyGcInv($freshAbs, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tj, Tk, Tk, Tl, $Time, $r1, $r2, true, $toAbs, $AbsMem, $GcMem, $gcSlice);
    assert RExtend(old($r2), $r2);
    ecx := section;
    if (ecx >= ?sectionCount) { goto loopEnd; }

    call scanStaticSectionCopy(section);
    call section := AddChecked(section, 1);
    goto loop;
  loopEnd:
}

procedure GarbageCollectCopying($ra:int, $nextFp:int)
  requires ecx == $ra && word($ra);
  requires edx == $nextFp;
  requires FrameNextInv($FrameCount, $ra, $nextFp, $FrameAddr, $FrameLayout);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  requires StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  requires $freshAbs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $freshAbs);

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $SectionMem, $FrameMem;
  modifies Ti, Tj, Tk, Tl, Fi, Fk, Fl, BF, BT;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  // postcondition same as precondition, plus reached:
  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $freshAbs);
  ensures  (forall i:int::{TV(i)} TV(i) ==> Fi <= i && i < Fk && $toAbs[i] != NO_ABS ==>
             reached($toAbs[i], $Time));
  ensures  ebp == old(ebp);
{
  var saveEbp:int;
  saveEbp := ebp;

  $r1 := $toAbs;
  $r2 := MAP_NO_ABS;
  eax := Ti;
  Tj := eax;
  Tk := eax;

  eax := BT;
  ebx := Fi;
  if (ebx != HeapLo) { goto skip1; }
    ebx := HeapLo;
    assert ?gcLo + BitIndex(HeapLo, Tl) == ebx;
    goto skip2;
  skip1:
    ebx := BF;
    assert ?gcLo + BitIndex(HeapLo, Tl) == ebx;
  skip2:
  assert TVM(32, (BitIndex(HeapLo, Fl) - BitIndex(HeapLo, Fi)));
  assert TVM(32, (BitIndex(HeapLo, Tl) - BitIndex(HeapLo, Ti)));

  esp := esp - 4; call BB4Zero($toAbs, 0, NO_ABS, Ti, Ti, Ti, Tl, 0, ?gcLo + BitIndex(HeapLo, Ti), ?gcLo + BitIndex(HeapLo, Tl), Fi, ?gcLo + BitIndex(HeapLo, Fi));

  call scanStackCopy($ra, $nextFp);
  call scanStaticCopy();
  call scanObjects();

  $toAbs := $r2;

  eax := Fi;
  ebx := Ti;
  Fi := ebx;
  Ti := eax;

  eax := Fl;
  ebx := Tl;
  Fl := ebx;
  Tl := eax;

  eax := Tk;
  Fk := eax;

  eax := Ti;
  Tk := eax;
  Tj := eax;

  eax := BF;
  ebx := BT;
  BF := ebx;
  BT := eax;

  ebp := saveEbp;
  esp := esp + 4; return;
}

procedure doAllocCopyingWord($ret:int, $ind:int)
  requires esi == $ret + 4 * $ind;

  requires TO($ind) && $ind >= 0;
  requires Aligned($ret) && Fk <= $ret && $ret + 4 * $ind + 4 <= Fl;
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  requires (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> $gcSlice[$ret + 4 * j] == $ret);
  requires (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> gcAddr($ret + 4 * j)); // REVIEW: necessary?
  requires (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> $GcMem[$ret + 4 * j] == NULL);

  modifies $GcMem, $gcSlice;

  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
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

procedure doAllocCopyingWords($ret:int, $size:int, $nf:int)
  requires eax == $ret;
  requires ebx == $ret + $size;
  requires $size == $nf * 4;
  requires $nf >= 0;
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  requires Aligned($ret) && Fk <= $ret && $ret + $size <= Fl;

  modifies $GcMem, $gcSlice;
  modifies esi;

  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
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
    assert MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> $gcSlice[$ret + 4 * j] == $ret);
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> gcAddr($ret + 4 * j)); // REVIEW: necessary?
    assert (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j < $ind ==> $GcMem[$ret + 4 * j] == NULL);

    call doAllocCopyingWord($ret, $ind);
    $ind := $ind + 1;
    call esi := Add(esi, 4);
    if (esi < ebx) { goto loop; }
  loopEnd:
}

procedure doAllocObjectCopying($ra:int, $nextFp:int, $abs:int, $vt:int, $size:int)
  requires eax == $size;
  requires ebx == Fk + $size;
  requires ecx == $vt;
  requires Fk + 4 * numFields($abs) <= Fl;
  requires !VFieldPtr($abs, 0);
  requires !VFieldPtr($abs, 1);
  requires 2 <= numFields($abs);
  requires $size == 4 * numFields($abs);
  requires ObjSize($abs, $vt, $AbsMem[$abs][2], $AbsMem[$abs][3]);
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);

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

  modifies $GcMem, $toAbs, $gcSlice, Fk;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  old($toAbs)[eax - 4] == NO_ABS;
  ensures  $toAbs == old($toAbs)[eax - 4 := $abs];
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  ebp == old(ebp);
{
  eax := Fk;

  assert TV(eax + 0) && TV(eax + 4);
  assert TO(1) && TO(2);
  assert TO(numFields($abs));

  call doAllocCopyingWords(eax, $size, numFields($abs));

  call GcStore(eax + 4, ecx);

  esi := eax;
  call esi := Sub(esi, Fi);
  edi := BF;
  call bb4SetBit($toAbs, $abs, NO_ABS, Fi, Fi, Fi, Fl, Fk, ?gcLo + BitIndex(HeapLo, Fi), ?gcLo + BitIndex(HeapLo, Fl));
  assert TV(Fk - Fi);

  $toAbs[eax] := $abs;
  assert TV(Fk);
  assert TO(numFields($abs));

  Fk := ebx;
  call eax := Add(eax, 4);

  assert TV(eax + 4);
  assert TO(0);
}

procedure doAllocStringCopying($ra:int, $nextFp:int, $abs:int, $vt:int, $nElems:int)
  requires ecx == pad(16 + 2 * $nElems);
  requires ebx == Fk + pad(16 + 2 * $nElems);
  requires edx == $nElems;
  requires $vt == ?STRING_VTABLE;
  requires Fk + pad(16 + 2 * $nElems) + 0 <= Fl;
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);

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

  modifies $GcMem, $toAbs, $gcSlice, Fk;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  old($toAbs)[eax - 4] == NO_ABS;
  ensures  $toAbs == old($toAbs)[eax - 4 := $abs];
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  ebp == old(ebp);
{
  eax := Fk;
  assert TV(eax + 0) && TV(eax + 4) && TV(eax + 8) && TV(eax + 12);
  assert TO(1) && TO(2) && TO(3);
  assert TVL($abs);
  assert TVT($abs, $vt);
  assert TO(numFields($abs));

  call doAllocCopyingWords(eax, pad(16 + 2 * $nElems), numFields($abs));

  call GcStore(eax + 8, edx);
  call edx := SubChecked(edx, 1);
  call GcStore(eax + 12, edx);
  edx := ?STRING_VTABLE;
  call GcStore(eax + 4, edx);

  esi := eax;
  call esi := Sub(esi, Fi);
  edi := BF;
  call bb4SetBit($toAbs, $abs, NO_ABS, Fi, Fi, Fi, Fl, Fk, ?gcLo + BitIndex(HeapLo, Fi), ?gcLo + BitIndex(HeapLo, Fl));
  assert TV(Fk - Fi);

  $toAbs[eax] := $abs;
  assert TV(Fk);
  assert TO(numFields($abs));

  Fk := ebx;
  call eax := Add(eax, 4);

  assert TV(eax + 4);
  assert TO(0);
}

procedure fromArrayInfo($abs:int, $vt:int)
  requires VTable($abs, $vt);
  requires tag($vt) == ?PTR_ARRAY_TAG || tag($vt) == ?OTHER_ARRAY_TAG;
  ensures  !VFieldPtr($abs, 0);
  ensures  !VFieldPtr($abs, 1);
  ensures  !VFieldPtr($abs, 2);
  ensures  !VFieldPtr($abs, 3);
{
  assert TO(0) && TO(1) && TO(2) && TO(3) && TO(4);
  assert TVL($abs);
  assert TVT($abs, $vt);
}

procedure doAllocArrayCopyingHelper($abs:int, $vt:int, $rank:int, $nElems:int)
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

procedure doAllocArrayCopying($ra:int, $nextFp:int, $abs:int, $vt:int, $rank:int, $nElems:int, $size:int)
//  requires eax == $size;
  requires ebx == Fk + $size;
  requires ecx == $vt;
  requires edx == $rank;
  requires esi == $nElems;
  requires Fk + 4 * numFields($abs) <= Fl;
  requires !VFieldPtr($abs, 0);
  requires !VFieldPtr($abs, 1);
  requires !VFieldPtr($abs, 2);
  requires !VFieldPtr($abs, 3);
  requires 4 <= numFields($abs);
  requires $size == 4 * numFields($abs);
  requires ObjSize($abs, $vt, $rank, $nElems);
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);

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

  modifies $GcMem, $toAbs, $gcSlice, Fk;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  old($toAbs)[eax - 4] == NO_ABS;
  ensures  $toAbs == old($toAbs)[eax - 4 := $abs];
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  ebp == old(ebp);
{
  var nElems:int;
  eax := Fk;
  nElems := esi;

  assert TV(eax + 0) && TV(eax + 4) && TV(eax + 8) && TV(eax + 12);
  assert TO(1) && TO(2) && TO(3) && TO(4);
  assert TO(numFields($abs));

  call doAllocCopyingWords(eax, $size, numFields($abs));

  esi := nElems;
  call GcStore(eax + 4, ecx);
  call GcStore(eax + 8, edx);
  call GcStore(eax + 12, esi);

  esi := eax;
  call esi := Sub(esi, Fi);
  edi := BF;
  call bb4SetBit($toAbs, $abs, NO_ABS, Fi, Fi, Fi, Fl, Fk, ?gcLo + BitIndex(HeapLo, Fi), ?gcLo + BitIndex(HeapLo, Fl));
  assert TV(Fk - Fi);

  $toAbs[eax] := $abs;
  assert TV(Fk);
  assert TO(numFields($abs));

  Fk := ebx;
  call eax := Add(eax, 4);

  assert TV(eax + 4);
  assert TO(0);
}

procedure doAllocVectorCopyingHelper($abs:int, $vt:int, $nElems:int)
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

procedure doAllocVectorCopying($ra:int, $nextFp:int, $abs:int, $vt:int, $nElems:int, $size:int)
//  requires eax == $size;
  requires ebx == Fk + $size;
  requires ecx == $vt;
  requires edx == $nElems;
  requires Fk + 4 * numFields($abs) <= Fl;
  requires !VFieldPtr($abs, 0);
  requires !VFieldPtr($abs, 1);
  requires !VFieldPtr($abs, 2);
  requires 3 <= numFields($abs);
  requires $size == 4 * numFields($abs);
  requires ObjSize($abs, $vt, $nElems, $AbsMem[$abs][3]);
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);

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

  modifies $GcMem, $toAbs, $gcSlice, Fk;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  old($toAbs)[eax - 4] == NO_ABS;
  ensures  $toAbs == old($toAbs)[eax - 4 := $abs];
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  ebp == old(ebp);
{
  eax := Fk;

  assert TV(eax + 0) && TV(eax + 4) && TV(eax + 8);
  assert TO(1) && TO(2) && TO(3);
  assert TO(numFields($abs));

  call doAllocCopyingWords(eax, $size, numFields($abs));

  call GcStore(eax + 4, ecx);
  call GcStore(eax + 8, edx);

  esi := eax;
  call esi := Sub(esi, Fi);
  edi := BF;
  call bb4SetBit($toAbs, $abs, NO_ABS, Fi, Fi, Fi, Fl, Fk, ?gcLo + BitIndex(HeapLo, Fi), ?gcLo + BitIndex(HeapLo, Fl));
  assert TV(Fk - Fi);

  $toAbs[eax] := $abs;
  assert TV(Fk);
  assert TO(numFields($abs));

  Fk := ebx;
  call eax := Add(eax, 4);

  assert TV(eax + 4);
  assert TO(0);
}

procedure doAllocObjectCopyingHelper($abs:int, $vt:int)
  requires ecx == $vt;
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, 0, 0);
  requires !isVarSize(tag($vt));
  modifies eax;
  ensures  !VFieldPtr($abs, 0);
  ensures  !VFieldPtr($abs, 1);
  ensures  2 <= numFields($abs);
  ensures  eax == 4 * numFields($abs);
  ensures  ObjSize($abs, $vt, $AbsMem[$abs][2], $AbsMem[$abs][3]);
{
  assert TO(2);
  assert TVL($abs);
  assert TVT($abs, $vt);
  call eax := RoLoad32(ecx + ?VT_BASE_LENGTH);
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
  modifies $toAbs, Ti, Tj, Tk, Tl, Fi, Fk, Fl, HeapLo, BF, BT;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $GcMem;
  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
{
  var save:int;
  var unitSize:int;
  save := ebp;

  // The heap consists of two bitmaps, followed by two semispaces:
  //   <--4--><--4--><--128--><--128-->
  // Each bit map must consist of at least 4 bytes.
  // For each bit in the bit map, there is one word in the corresponding semispace.
  // Thus, the total gc memory size must be a multiple of:
  //   4 + 4 + 128 + 128 = 8 + 256 = 264 bytes

  // Compute gcMem size, in bytes and words
  esi := ?gcHi;
  call esi := Sub(esi, ?gcLo);
  edi := esi;

  // Break into 264-byte units.  Let ebp be the number of units.
  edx := 0;
  eax := edi;
  ebx := 264;
  call eax, edx := Div(eax, edx, ebx);
  ebp := eax;
  unitSize := ebp;
  assert 264 * unitSize <= (?gcHi - ?gcLo);

  // Divide heap into ?gcLo <--4--> eax <--4--> ebx <--128--> ecx <--128--> ?gcHi
  edx := 0;
  call ebp := Lea(edx + 4 * ebp);
  eax := ?gcLo;
  BF := eax;
  call eax := Add(eax, ebp);
  BT := eax;
  call ebx := Lea(eax + ebp);
  call ebp := Lea(edx + 4 * ebp);
  call ecx := Lea(ebx + 8 * ebp);
  call edx := Lea(ecx + 8 * ebp);

  $toAbs := MAP_NO_ABS;
  HeapLo := ebx;
  Fi := ebx;
  Fk := ebx;
  Fl := ecx;
  Ti := ecx;
  Tj := ecx;
  Tk := ecx;
  Tl := edx;

  call __initialize(unitSize, HeapLo);

  assert TV(?gcLo);
  assert TV(HeapLo);
  assert TO(0);
  assert TO(unitSize);
  assert TO(2 * unitSize);
  assert TO(32 * unitSize);
  eax := ?gcLo;
  esi := unitSize;
  call ebx := Lea(eax + 4 * esi);
  esp := esp - 4; call BB4Zero($toAbs, 0, NO_ABS, Fi, Fi, Fi, Fl, 0, ?gcLo, ?gcLo + 4 * unitSize, 0, 0);

  assert TVM(32, (BitIndex(HeapLo, Fl) - BitIndex(HeapLo, Fi)));
  assert TVM(32, (BitIndex(HeapLo, Tl) - BitIndex(HeapLo, Ti)));

  ebp := save;
  esp := esp + 4; return;
}

// Prepare to call GcLoad (don't actually call it -- let the mutator call it)
procedure readCopying($ptr:int, $fld:int) returns ($val:int)
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
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

procedure writeCopying($ptr:int, $fld:int, $val:int, $abs:int) returns ($_gcData:[int]int, $_absData:[int][int]int)
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  requires Pointer($toAbs, $ptr, $toAbs[$ptr]);
  requires 0 <= $fld && $fld < numFields($toAbs[$ptr]);
  requires !isReadonlyField(tag($AbsMem[$toAbs[$ptr]][1]), $fld);
  requires Value(VFieldPtr($toAbs[$ptr], $fld), $toAbs, $val, $abs);
  ensures  gcAddr($ptr + 4 * $fld);
  ensures  word($val);
  ensures  $_gcData == $GcMem[$ptr + 4 * $fld := $val];
  ensures  $_absData == $AbsMem[$toAbs[$ptr] := $AbsMem[$toAbs[$ptr]][$fld := $abs]];
  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $_gcData, $toAbs, $_absData, $gcSlice);
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
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);

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

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $SectionMem, $FrameMem, $freshAbs;
  modifies Ti, Tj, Tk, Tl, Fi, Fk, Fl, BF, BT;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
{
  var size:int;
  var vt:int;
  call doAllocObjectCopyingHelper($abs, $vt);

  $freshAbs := $abs;

  ebx := Fk;
  call ebx := AddChecked(ebx, eax);

  //if (!(Fk + size <= Fl))
  if (ebx <= Fl) { goto skip1; }
    size := eax;
    vt := ecx;

    call ecx := FrameLoad(($FrameCount), esp);
    edx := ebp;
    esp := esp - 4; call GarbageCollectCopying($ra, ebp);

    eax := size;
    ecx := vt;

    ebx := Fk;
    call ebx := AddChecked(ebx, eax);
    if (ebx <= Fl) { goto skip1; }
      // Out of memory
      call DebugBreak();
  skip1:

  call doAllocObjectCopying($ra, ebp, $abs, $vt, eax);
  esp := esp + 4; return;
}

procedure AllocString($ra:int, $abs:int, $vt:int, $nElems:int)
  // GC invariant:
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);

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

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $SectionMem, $FrameMem, $freshAbs;
  modifies Ti, Tj, Tk, Tl, Fi, Fk, Fl, BF, BT;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
{
  var size:int;
  var nElems:int;

  $freshAbs := $abs;

  call ecx := AddChecked(ecx, 1);
  edx := ecx;
  call ecx := AddChecked(ecx, ecx);
  call ecx := AddChecked(ecx, 19);
  eax := 3;
  call eax := Not(eax);
  call ecx := And(ecx, eax);
  ebx := Fk;
  call ebx := AddChecked(ebx, ecx);
  //if (!(Fk + pad(16 + 2 * $nElems) + 0 <= Fl))
  if (ebx <= Fl) { goto skip1; }
    size := ecx;
    nElems := edx;

    call ecx := FrameLoad(($FrameCount), esp);
    edx := ebp;
    esp := esp - 4; call GarbageCollectCopying($ra, ebp);

    ecx := size;
    edx := nElems;
    ebx := Fk;
    call ebx := AddChecked(ebx, ecx);
    if (ebx <= Fl) { goto skip1; }
      // Out of memory
      call DebugBreak();
  skip1:

  call doAllocStringCopying($ra, ebp, $abs, $vt, $nElems);
  esp := esp + 4; return;
}

procedure AllocArray($ra:int, $abs:int, $vt:int, $rank:int, $nElems:int)
  // GC invariant:
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);

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

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $SectionMem, $FrameMem, $freshAbs;
  modifies Ti, Tj, Tk, Tl, Fi, Fk, Fl, BF, BT;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
{
  var vt:int;
  var rank:int;
  var size:int;
  var nElems:int;

  $freshAbs := $abs;

  call esi := FrameLoad(($FrameCount), esp + 4);

  rank := edx;
  call doAllocArrayCopyingHelper($abs, $vt, $rank, $nElems);
  ebx := Fk;
  call ebx := AddChecked(ebx, eax);

  //if (!(Fk + size <= Fl))
  if (ebx <= Fl) { goto skip1; }
    size := eax;
    vt := ecx;
    nElems := esi;

    call ecx := FrameLoad(($FrameCount), esp);
    edx := ebp;
    esp := esp - 4; call GarbageCollectCopying($ra, ebp);

    eax := size;
    ecx := vt;
    esi := nElems;
    ebx := Fk;
    call ebx := AddChecked(ebx, eax);
    if (ebx <= Fl) { goto skip1; }
      // Out of memory
      call DebugBreak();
  skip1:

  edx := rank;
  call doAllocArrayCopying($ra, ebp, $abs, $vt, $rank, $nElems, eax);
  esp := esp + 4; return;
}

procedure AllocVector($ra:int, $abs:int, $vt:int, $nElems:int)
  // GC invariant:
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);

  // requirements on mutator root layout:
  requires 0 <= $FrameCount;
  requires $FrameSlice[esp] == $FrameCount && $FrameMem[esp] == $ra;
  requires FrameNextInv($FrameCount, $ra, ebp, $FrameAddr, $FrameLayout);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  requires StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  requires MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);

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

  modifies $r1, $r2, $GcMem, $toAbs, $gcSlice, $SectionMem, $FrameMem, $freshAbs;
  modifies Ti, Tj, Tk, Tl, Fi, Fk, Fl, BF, BT;
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;

  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs, $Time);
  ensures  StackInv($toAbs, $FrameCount, $FrameAddr, $FrameLayout, $FrameSlice, $FrameMem, $FrameAbs, $FrameOffset, $Time);
  ensures  MutatorInv(BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl, $GcMem, $toAbs, $AbsMem, $gcSlice);
  ensures  Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
{
  var size:int;
  var vt:int;
  var nElems:int;

  nElems := edx;
  call doAllocVectorCopyingHelper($abs, $vt, $nElems);

  $freshAbs := $abs;

  ebx := Fk;
  call ebx := AddChecked(ebx, eax);

  //if (!(Fk + size <= Fl))
  if (ebx <= Fl) { goto skip1; }
    size := eax;
    vt := ecx;

    call ecx := FrameLoad(($FrameCount), esp);
    edx := ebp;
    esp := esp - 4; call GarbageCollectCopying($ra, ebp);

    eax := size;
    ecx := vt;

    ebx := Fk;
    call ebx := AddChecked(ebx, eax);
    if (ebx <= Fl) { goto skip1; }
      // Out of memory
      call DebugBreak();
  skip1:

  edx := nElems;
  call doAllocVectorCopying($ra, ebp, $abs, $vt, $nElems, eax);
  esp := esp + 4; return;
}


//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// Common definitions and procedures shared between garbage collectors.
// This file is included by the garbage collectors.

// Imports:
//   - Trusted.bpl
//   - VerifiedBitVectors.bpl

// Imported from VerifiedBitVectors.bpl:
function BitIndex(i0:int, i:int) returns(int);
function BitZero(x:int, i0:int, i:int) returns(bool);
function ColorIndex(i0:int, i:int) returns(int);
function ColorGet(x:int, i0:int, i:int) returns(int);

/*****************************************************************************
******************************************************************************
**** VERIFIED
******************************************************************************
*****************************************************************************/

function AlignedHeapAddr(i:int) returns(bool) { gcAddr(i) && Aligned(i) }

//////////////////////////////////////////////////////////////////////////////
// LOCAL REASONING
//////////////////////////////////////////////////////////////////////////////

// As a region evolves, it adds new mappings, but each mapping is
// permanent: RExtend ensures that new mappings do not overwrite old mappings.
function RExtend(rOld:[int]int, rNew:[int]int) returns (bool)
{
  (forall i:int::{rOld[i]}{rNew[i]} rOld[i] != NO_ABS ==> rOld[i] == rNew[i])
}

function AbsMapped(val:int, rev:[int]int, abs:int) returns (bool)
{
  abs != NO_ABS && abs == rev[val]
}

// Both the mark-sweep and copying collectors only have two regions at
// any given time.
var $r1:[int]int;
var $r2:[int]int;

//////////////////////////////////////////////////////////////////////////////
// OBJECTS
//////////////////////////////////////////////////////////////////////////////

// Each object occupies a "slice" of the heap.  If an object occupies
// addresses i + 0 ... i + m, then slice[i + 0] == i && ... && slice[i + m] == i.
// This helps distinguish addresses that belong to different objects.
var $gcSlice:[int]int;

// REVIEW: cut $toAbs here?
function ObjInvBase(i:int, rs:[int]int, $toAbs:[int]int,
  $AbsMem:[int][int]int, $GcMem:[int]int, $gcSlice:[int]int) returns (bool)
{
  gcAddr(i) && rs[i] != NO_ABS ==>
      Aligned(i)
   && AlignedHeapAddr(i + 4) // REVIEW: this is convenient, but is it necessary?
   && VTable(rs[i], $AbsMem[rs[i]][1])
   && !VFieldPtr(rs[i], 1) // REVIEW: necessary?
   && numFields(rs[i]) >= 2 // REVIEW: necessary?
   && ObjSize(rs[i], $AbsMem[rs[i]][1], $AbsMem[rs[i]][2], $AbsMem[rs[i]][3])
   && $gcSlice[i] == i
   && $gcSlice[i + 4] == i // REVIEW: this is convenient, but is it necessary?
}

function ObjInvField(i:int, j:int, rs:[int]int, rt:[int]int, $toAbs:[int]int,
  $AbsMem:[int][int]int, $GcMem:[int]int, $gcSlice:[int]int) returns (bool)
{
  gcAddr(i) && rs[i] != NO_ABS ==>
      gcAddr(i + 4 * j) // REVIEW: necessary?
   && $gcSlice[i + 4 * j] == i
   && Value(VFieldPtr(rs[i], j), rt, $GcMem[i + 4 * j], $AbsMem[$toAbs[i]][j])
}

function ObjInvPartial(i:int, j1:int, j2:int, rs:[int]int, rt:[int]int, $toAbs:[int]int,
  $AbsMem:[int][int]int, $GcMem:[int]int, $gcSlice:[int]int) returns (bool)
{
      ObjInvBase(i, rs, $toAbs, $AbsMem, $GcMem, $gcSlice)
   && (forall j:int::{TO(j)} TO(j) ==> j1 <= j && j < j2 ==>
        ObjInvField(i, j, rs, rt, $toAbs, $AbsMem, $GcMem, $gcSlice))
}

function ObjInv(i:int, rs:[int]int, rt:[int]int, $toAbs:[int]int, $AbsMem:[int][int]int,
  $GcMem:[int]int, $gcSlice:[int]int) returns (bool)
{
  ObjInvPartial(i, 0, numFields(rs[i]), rs, rt, $toAbs, $AbsMem, $GcMem, $gcSlice)
}

procedure TableSearch($base:int, $count:int, $x:int)
  requires ecx == $base && edx == $count && ebp == $x;
  requires word(ecx) && word(edx) && word(ebp);
  requires (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j <= $count ==> inRo($base + 4 * j, 4));
  requires (forall j1:int, j2:int::{TO(j1), TO(j2)} TO(j1) && TO(j2) ==> 0 <= j1 && j1 < j2 && j2 <= $count ==>
    ro32($base + 4 * j1) < ro32($base + 4 * j2));
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  // eax = ret
  // edx = found
  ensures edx != 0 <==> (exists j:int::{TO(j)} TO(j) && 0 <= j && j < $count && between(ro32($base + 4 * j), ro32($base + 4 * (j + 1)), $x));
  ensures edx != 0  ==> 0 <= eax && eax < $count && between(ro32($base + 4 * eax), ro32($base + 4 * (eax + 1)), $x);
{
  if (edx >= 0) { goto skip1; }
    edx := 0;
    esp := esp + 4; return;
  skip1:

  assert TO(0);
  call eax := RoLoad32(ecx);
  if (ebp >= eax) { goto skip2; }
    assert TO(0);
    edx := 0;
    esp := esp + 4; return;
  skip2:

  assert TO($count);
  call eax := RoLoad32(ecx + 4 * edx);
  if (ebp < eax) { goto skip3; }
    assert TO($count);
    // REVIEW: can this be cleaned up?
    assert (forall j:int::{TSlot(j)} TSlot(j) && TO(j) && TO(j + 1) && 0 <= j && j < $count ==> $x >= ro32($base + 4 * (j + 1)));
    assert (forall j:int::{TO(j)} TO(j) && TSlot(j) && 0 <= j && j < $count ==> $x >= ro32($base + 4 * (j + 1)));
    edx := 0;
    esp := esp + 4; return;
  skip3:

  esi := 0;
  edi := edx;

//  while (esi + 1 < edi)
  loop:
    assert TO(esi) && TO(edi) && 0 <= esi && esi < edi && edi <= $count;
    assert (exists j:int::{TO(j)} TO(j) && 0 <= j && j < $count && between(ro32($base + 4 * j), ro32($base + 4 * (j + 1)), $x)) ==>
      ro32($base + 4 * esi) <= $x && $x < ro32($base + 4 * edi);
    call eax := Lea(esi + 1);
    if (eax >= edi) { goto loopEnd; }

    call ebx := LeaUnchecked(esi + 1 * edi);
    call ebx := Shr(ebx, 1);
    if (ebx <= esi) { goto do4; }
    if (ebx >= edi) { goto do4; }
    goto skip4;
    do4:
      call ebx := Lea(esi + 1);
    skip4:

    assert TO(ebx);
    call eax := RoLoad32(ecx + 4 * ebx);
    if (eax <= ebp) { goto do5; }
      edi := ebx;
    goto skip5;
    do5:
      esi := ebx;
    skip5:
    goto loop;
  loopEnd:

  eax := esi;
  call ebx := RoLoad32(ecx + 4 * eax);
  if (ebp < ebx) { goto skip6; }
  call ebx := RoLoad32(ecx + 4 * eax + 4);
  if (ebp >= ebx) { goto skip6; }
    edx := 1;
    esp := esp + 4; return;
  skip6:
    edx := 0;
    esp := esp + 4; return;
}

procedure TablesSearch($f:int, $ra:int, $nextFp:int)
  requires ecx == $ra && edx == $nextFp;
  requires word($ra);
  requires FrameNextInv($f, $ra, $nextFp, $FrameAddr, $FrameLayout);
  modifies eax, ebx, ecx, edx, esi, edi, ebp, esp;
  // eax = ret
  // edx = found
  ensures  edx != 0 ==> $f > 0 && eax == frameDescriptor($FrameLayout[$f - 1]) && $FrameAddr[$f - 1] == $nextFp;
  ensures  edx == 0 ==> $f == 0;
{
  var ra:int;
  var nextFp:int;
  var table:int;
  var index:int;
  var tableBase:int;
  var tmp1:int;
  var tmp2:int;
  ra := ecx;
  nextFp := edx;
  table := 0;
  edx := 0;

  //while (table < ?callSiteTableCount)
  loop:
    assert TVFT($f);
    assert TT(table) && 0 <= table;
    assert edx == 0;
    assert !(exists t:int, j:int::{TT(t), TO(j)} TT(t) && TO(j) && t < table && RetAddrAt(t, j, ra));
    assert word(table) && word(ra);
    eax := table;
    if (?callSiteTableCount <= eax) { goto loopEnd; }

    ebx := ?returnAddressToCallSiteSetNumbers;
    call ecx := RoLoad32(ebx + 4 * eax);
    ebx := ?callSiteSetCount;
    call edx := RoLoad32(ebx + 4 * eax);
    call edx := RoLoad32(edx);
    ebx := ?codeBaseStartTable;
    call esi := RoLoad32(ebx + 4 * eax);

    ebp := ra;

    assert TO(0);
    call eax := RoLoad32(ecx); // REVIEW: better way to prove word(ro32(ecx)).

    if (esi > ebp) { goto skip1; }
      call ebp := Sub(ebp, esi);
      esp := esp - 4; call TableSearch(ecx, edx, ra - esi);
      index := eax;

    assert TO(index);
    if (edx == 0) { goto skip1; }
      esi := table;
      edi := ?activationDescriptorTable;
      call ecx := RoLoad32(edi + 4 * esi);
      edi := ?callSiteSetNumberToIndex;
      call ebp := RoLoad32(edi + 4 * esi);
      call ebp := RoLoadU16(ebp + 2 * eax);
      call eax := RoLoad32(ecx + 4 * ebp);
      esp := esp + 4; return;
    skip1:

    call table := AddChecked(table, 1);
    edx := 0;
    goto loop;
  loopEnd:
    esp := esp + 4; return;
}

procedure getSize($abs:int, $ptr:int, $vt:int, $_nElems1:int, $_nElems2:int)
  requires ecx == $ptr && edx == $vt;
  requires ObjSize($abs, $vt, $_nElems1, $_nElems2);
  requires VTable($abs, $vt);
  requires numFields($abs) >= 3 ==> AlignedHeapAddr($ptr + 8);
  requires numFields($abs) >= 3 && !VFieldPtr($abs, 2) ==> $GcMem[$ptr + 8] == $_nElems1;
  requires numFields($abs) >= 4 ==> AlignedHeapAddr($ptr + 12);
  requires numFields($abs) >= 4 && !VFieldPtr($abs, 3) ==> $GcMem[$ptr + 12] == $_nElems2;
  modifies eax, ebx, edx, esi, edi, ebp, esp;
  ensures  eax == 4 * numFields($abs);
{
  assert TVL($abs);
  assert TVT($abs, $vt);
  call ebp := RoLoad32(edx + ?VT_MASK);
  call ebp := And(ebp, 15);

  if (ebp != ?SPARSE_TAG) { goto skip1; }
    call eax := RoLoad32(edx + ?VT_BASE_LENGTH);
    goto end;
  skip1:

  if (ebp != ?DENSE_TAG) { goto skip2; }
    call eax := RoLoad32(edx + ?VT_BASE_LENGTH);
    goto end;
  skip2:

  if (ebp != ?STRING_TAG) { goto skip3; }
    assert TO(2);
    call esi := GcLoad(ecx + 8);
    //eax := pad(16 + 2 * esi);
    eax := esi;
    call eax := AddChecked(eax, eax);
    call eax := AddChecked(eax, 19);
    ebx := 3;
    call ebx := Not(ebx);
    call eax := And(eax, ebx);
    goto end;
  skip3:

  if (ebp != ?PTR_VECTOR_TAG) { goto skip4; }
    assert TO(2);
    call esi := GcLoad(ecx + 8);
    call eax := RoLoad32(edx + ?VT_BASE_LENGTH);
    //eax := pad(eax + 4 * esi);
    call esi := AddChecked(esi, esi);
    call esi := AddChecked(esi, esi);
    call eax := AddChecked(eax, esi);
    call eax := AddChecked(eax, 3);
    ebx := 3;
    call ebx := Not(ebx);
    call eax := And(eax, ebx);
    goto end;
  skip4:

  if (ebp != ?OTHER_VECTOR_TAG) { goto skip5; }
    assert TO(2);
    call esi := GcLoad(ecx + 8);
    call eax := RoLoad32(edx + ?VT_BASE_LENGTH);
    call ebx := RoLoad32(edx + ?VT_ARRAY_ELEMENT_SIZE);
    //eax := pad(eax + Mult(ebx, esi));
    ebp := eax;
    eax := ebx;
    call eax, edx := MulChecked(eax, esi);
    call eax := AddChecked(eax, ebp);
    call eax := AddChecked(eax, 3);
    ebx := 3;
    call ebx := Not(ebx);
    call eax := And(eax, ebx);
    goto end;
  skip5:

  if (ebp != ?PTR_ARRAY_TAG) { goto skip6; }
    assert TO(3);
    call esi := GcLoad(ecx + 12);
    call eax := RoLoad32(edx + ?VT_BASE_LENGTH);
    //eax := pad(eax + 4 * esi);
    call esi := AddChecked(esi, esi);
    call esi := AddChecked(esi, esi);
    call eax := AddChecked(eax, esi);
    call eax := AddChecked(eax, 3);
    ebx := 3;
    call ebx := Not(ebx);
    call eax := And(eax, ebx);
    goto end;
  skip6:

  if (ebp != ?OTHER_ARRAY_TAG) { goto skip7; }
    assert TO(3);
    call esi := GcLoad(ecx + 12);
    call eax := RoLoad32(edx + ?VT_BASE_LENGTH);
    call ebx := RoLoad32(edx + ?VT_ARRAY_ELEMENT_SIZE);
    //eax := pad(eax + Mult(ebx, esi));
    ebp := eax;
    eax := ebx;
    call eax, edx := MulChecked(eax, esi);
    call eax := AddChecked(eax, ebp);
    call eax := AddChecked(eax, 3);
    ebx := 3;
    call ebx := Not(ebx);
    call eax := And(eax, ebx);
    goto end;
  skip7:

  // else
    call eax := RoLoad32(edx + ?VT_BASE_LENGTH);
  end:
}

procedure GetSize($ptr:int, $vt:int, $rs:[int]int, $rt:[int]int)
  requires ecx == $ptr && edx == $vt;
  requires gcAddr($ptr);
  requires $rs[$ptr] != NO_ABS && $rs[$ptr] == $toAbs[$ptr];
  requires ObjInv($ptr, $rs, $rt, $toAbs, $AbsMem, $GcMem, $gcSlice);
  requires $vt == $AbsMem[$rs[$ptr]][1] || $vt == $GcMem[$ptr + 4];
  modifies eax, ebx, edx, esi, edi, ebp, esp;
  ensures  eax == 4 * numFields($rs[$ptr]);
{
  assert TV($ptr);
  assert TO(1);
  assert TO(2);
  assert TO(3);
  call getSize($rs[$ptr], $ptr, $vt, $AbsMem[$rs[$ptr]][2], $AbsMem[$rs[$ptr]][3]);
  esp := esp + 4; return;
}

procedure readTag($abs:int, $vt:int)
  requires ecx == $vt;
  requires VTable($abs, $vt);
  modifies eax;
  ensures  eax == tag($vt);
{
  assert TVT($abs, $vt);
  call eax := RoLoad32(ecx + ?VT_MASK);
  call eax := And(eax, 15);
}

procedure readArrayOf($abs:int, $vt:int)
  requires ecx == $vt;
  requires VTable($abs, $vt);
  modifies ebp;
  ensures ebp == arrayOf($vt);
{
  assert TVT($abs, $vt);
  call ebp := RoLoad32(ecx + ?VT_ARRAY_OF);
}

procedure readElementInfo($abs:int, $vt:int)
  requires ecx == $vt;
  requires VTable($abs, $vt);
  requires tag($vt) == ?OTHER_VECTOR_TAG;
  modifies esi, edi;
  ensures esi == arrayElementSize($vt);
  ensures edi == mask(arrayElementClass($vt));
{
  assert TVT($abs, $vt);
  call esi := RoLoad32(ecx + ?VT_ARRAY_ELEMENT_SIZE);
  call edi := RoLoad32(ecx + ?VT_ARRAY_ELEMENT_CLASS);
  call edi := RoLoad32(edi + ?VT_MASK);
}



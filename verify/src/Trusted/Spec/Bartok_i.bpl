//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

//////////////////////////////////////////////////////////////////////////////
// TRIGGERS
//////////////////////////////////////////////////////////////////////////////

// TSlot is a trigger for slots in sparse tags
function{:expand false} TSlot(slot:int) returns (bool) { true }

// TT is a trigger for tables
function{:expand false} TT(table:int) returns (bool) { true }

//////////////////////////////////////////////////////////////////////////////
// BARTOK INTERFACE
//////////////////////////////////////////////////////////////////////////////

function getBit(x:int, i:int) returns(bool) { 1 == and(shr(x, i), 1) }
function getNib(x:int, i:int) returns(int) { and(shr(x, i), 15) }

const ?SPARSE_TAG:int;        axiom ?SPARSE_TAG              == 1;
const ?DENSE_TAG:int;         axiom ?DENSE_TAG               == 3;
const ?PTR_VECTOR_TAG:int;    axiom ?PTR_VECTOR_TAG          == 5;
const ?OTHER_VECTOR_TAG:int;  axiom ?OTHER_VECTOR_TAG        == 7;
const ?PTR_ARRAY_TAG:int;     axiom ?PTR_ARRAY_TAG           == 9;
const ?OTHER_ARRAY_TAG:int;   axiom ?OTHER_ARRAY_TAG         == 11;
const ?STRING_TAG:int;        axiom ?STRING_TAG              == 13;

function isOtherTag(t:int) returns(bool)
{
 !(
      t == ?SPARSE_TAG || t == ?DENSE_TAG
   || t == ?PTR_VECTOR_TAG || t == ?OTHER_VECTOR_TAG
   || t == ?PTR_ARRAY_TAG  || t == ?OTHER_ARRAY_TAG
   || t == ?STRING_TAG
  )
}

function isVarSize(t:int) returns(bool)
{
    t == ?PTR_VECTOR_TAG || t == ?OTHER_VECTOR_TAG
 || t == ?PTR_ARRAY_TAG  || t == ?OTHER_ARRAY_TAG
 || t == ?STRING_TAG
}

function isReadonlyField(t:int, j:int) returns(bool)
{
    (j == 1)
 || (t == ?PTR_VECTOR_TAG && j == 2)
 || (t == ?OTHER_VECTOR_TAG && j == 2)
 || (t == ?PTR_ARRAY_TAG && (j == 2 || j == 3))
 || (t == ?OTHER_ARRAY_TAG && (j == 2 || j == 3))
 || (t == ?STRING_TAG && j == 2)
}

const ?STRING_VTABLE:int;
const ?BYTE_VECTOR_VTABLE:int;

const ?VT_MASK:int;                axiom ?VT_MASK == 60;
const ?VT_BASE_LENGTH:int;         axiom ?VT_BASE_LENGTH == 52;
const ?VT_ARRAY_ELEMENT_SIZE:int;  axiom ?VT_ARRAY_ELEMENT_SIZE == 44;
const ?VT_ARRAY_ELEMENT_CLASS:int; axiom ?VT_ARRAY_ELEMENT_CLASS == 40;
const ?VT_ARRAY_OF:int;            axiom ?VT_ARRAY_OF == 36;

function mask(vt:int) returns(int) { ro32(vt + ?VT_MASK) }
function tag(vt:int) returns(int) { and(mask(vt), 15) }
function baseLength(vt:int) returns(int) { ro32(vt + ?VT_BASE_LENGTH) }
function arrayElementSize(vt:int) returns(int) { ro32(vt + ?VT_ARRAY_ELEMENT_SIZE) }
function arrayElementClass(vt:int) returns(int) { ro32(vt + ?VT_ARRAY_ELEMENT_CLASS) }
function arrayOf(vt:int) returns(int) { ro32(vt + ?VT_ARRAY_OF) }

function baseWords(vt:int) returns(int) { shr(baseLength(vt), 2) }
function arrayElementWords(vt:int) returns(int) { shr(arrayElementSize(vt), 2) }

const ?TYPE_STRUCT:int; axiom ?TYPE_STRUCT == 3;

//  true ==> field j is pointer
// false ==> field j is primitive
function VFieldPtr(abs:int, f:int) returns(bool);

function fieldToSlot(vt:int, j:int) returns(k:int);

// field 0 is the first non-header field
function Sparse1(abs:int, vt:int, j:int, field:int) returns(bool)
{
    VFieldPtr(abs, j) == (fieldToSlot(vt, field) != 0)
 && (fieldToSlot(vt, field) != 0 ==> between(1, 8, fieldToSlot(vt, field))
     && getNib(mask(vt), 4 * fieldToSlot(vt, field)) - 1 == field)
}

function Sparse2(vt:int, nFields:int) returns(bool)
{
  (forall k:int::{TSlot(k)} TSlot(k) ==> 1 <= k && k < 8 && getNib(mask(vt), 4 * k) != 0 ==>
      between(0, nFields, getNib(mask(vt), 4 * k) - 1)
   && fieldToSlot(vt, getNib(mask(vt), 4 * k) - 1) == k)
}

function{:expand false} TVT(abs:int, vt:int) returns(bool) { true }
function VTable(abs:int, vt:int) returns(bool);
axiom (forall abs:int, vt:int::{TVT(abs, vt)} VTable(abs, vt) ==
(
    !VFieldPtr(abs, 0) // REVIEW: is this redundant?
 && !VFieldPtr(abs, 1) // REVIEW: is this redundant?
 && (tag(vt) == ?DENSE_TAG ==> (forall j:int::{TO(j)} TO(j) ==> 2 <= j && j < numFields(abs) ==>
      VFieldPtr(abs, j) == (j < 30 && getBit(mask(vt), 2 + j))) // REVIEW: is the "j < 30" redundant?
    )
 && (tag(vt) == ?SPARSE_TAG ==>
        (forall j:int::{TO(j)} TO(j) ==> Sparse1(abs, vt, j, j - 2))
     && Sparse2(vt, numFields(abs) - 2)
    )
 && (tag(vt) == ?STRING_TAG ==>
      (forall j:int::{TO(j)} TO(j) ==> !VFieldPtr(abs, j))
    )
 && (tag(vt) == ?PTR_VECTOR_TAG ==>
        between(3, numFields(abs), baseWords(vt))
     && (forall j:int::{TO(j)} TO(j) ==> (baseWords(vt) <= j && j < numFields(abs) <==> VFieldPtr(abs, j)))
    )
 && (tag(vt) == ?OTHER_VECTOR_TAG ==>
        !VFieldPtr(abs, 2)
     && inRo(arrayElementClass(vt) + ?VT_MASK, 4) // REVIEW
     && between(3, numFields(abs), baseWords(vt))
     && (arrayOf(vt) != ?TYPE_STRUCT ==> (forall j:int::{TO(j)} TO(j) ==> !VFieldPtr(abs, j)))
     && (arrayOf(vt) == ?TYPE_STRUCT ==> !isVarSize(tag(arrayElementClass(vt))))
     && (arrayOf(vt) == ?TYPE_STRUCT && mask(arrayElementClass(vt)) == ?SPARSE_TAG ==>
          (forall j:int::{TO(j)} TO(j) ==> !VFieldPtr(abs, j))) // REVIEW: redundant
     && (arrayOf(vt) == ?TYPE_STRUCT && tag(arrayElementClass(vt)) == ?SPARSE_TAG ==>
            (forall j:int::{TO(j)} TO(j) ==>
                (VFieldPtr(abs, j) ==> baseWords(vt) <= j && j < numFields(abs))
             && (baseWords(vt) <= j && j < numFields(abs) ==>
                  (forall m:int::{TO(m)} TO(m) ==>
                    between(0, arrayElementWords(vt), j - Mult(arrayElementWords(vt), m) - baseWords(vt)) ==>
                        baseWords(vt) + Mult(arrayElementWords(vt), m) + arrayElementWords(vt) <= numFields(abs)
                     && Sparse1(abs, arrayElementClass(vt), j, j - Mult(arrayElementWords(vt), m) - baseWords(vt)))))
         && arrayElementWords(vt) >= 0
         && Sparse2(arrayElementClass(vt), arrayElementWords(vt)))
    )
 && (tag(vt) == ?PTR_ARRAY_TAG ==>
        between(4, numFields(abs), baseWords(vt))
     && (forall j:int::{TO(j)} TO(j) ==> (baseWords(vt) <= j && j < numFields(abs) <==> VFieldPtr(abs, j)))
    )
 && (tag(vt) == ?OTHER_ARRAY_TAG ==>
        !VFieldPtr(abs, 2)
     && !VFieldPtr(abs, 3)
     && between(4, numFields(abs), baseWords(vt))
     && (arrayOf(vt) != ?TYPE_STRUCT ==> (forall j:int::{TO(j)} TO(j) ==> !VFieldPtr(abs, j)))
    )
 && (isOtherTag(tag(vt)) ==>
        (forall j:int::{TO(j)} TO(j) ==>
            VFieldPtr(abs, j) == (fieldToSlot(vt, j) != 0)
         && (fieldToSlot(vt, j) != 0 ==> between(1, 1 + ro32(mask(vt)), fieldToSlot(vt, j))
             && ro32(mask(vt) + 4 * fieldToSlot(vt, j)) + 1 == j))
     && (forall k:int::{TSlot(k)} TSlot(k) ==> 1 <= k && k < 1 + ro32(mask(vt)) ==>
            inRo(mask(vt) + 4 * k, 4)
         && (ro32(mask(vt) + 4 * k) != 0 ==>
                between(0, numFields(abs), ro32(mask(vt) + 4 * k) + 1)
             && fieldToSlot(vt, ro32(mask(vt) + 4 * k) + 1) == k))
     && inRo(mask(vt), 4)
     && ro32(mask(vt)) >= 0
    )
));

function pad(i:int) returns(int)
{
  and(i + 3, neg(3))
}

function{:expand false} TVL(abs:int) returns(bool) { true }
function ObjSize(abs:int, vt:int, nElems1:int, nElems2:int) returns(bool);
axiom (forall abs:int, vt:int, nElems1:int, nElems2:int::{TVL(abs), ObjSize(abs, vt, nElems1, nElems2)} ObjSize(abs, vt, nElems1, nElems2) ==
(
    numFields(abs) >= 2
 && (!isVarSize(tag(vt)) ==> 4 * numFields(abs) == baseLength(vt))
 && (tag(vt) == ?STRING_TAG ==> numFields(abs) >= 4 && 4 * numFields(abs) == pad(16 + 2 * nElems1))
 && (tag(vt) == ?PTR_VECTOR_TAG ==> numFields(abs) >= 3 && 4 * numFields(abs) == pad(baseLength(vt) + 4 * nElems1))
 && (tag(vt) == ?OTHER_VECTOR_TAG ==> numFields(abs) >= 3 && 4 * numFields(abs) == pad(baseLength(vt) + Mult(arrayElementSize(vt), nElems1)))
 && (tag(vt) == ?PTR_ARRAY_TAG ==> numFields(abs) >= 4 && 4 * numFields(abs) == pad(baseLength(vt) + 4 * nElems2))
 && (tag(vt) == ?OTHER_ARRAY_TAG ==> numFields(abs) >= 4 && 4 * numFields(abs) == pad(baseLength(vt) + Mult(arrayElementSize(vt), nElems2)))
));

type $FrameLayout;
function frameLayoutArgs(l:$FrameLayout) returns(int);
function frameLayoutLocals(l:$FrameLayout) returns(int);
function frameHasPtr(l:$FrameLayout, j:int) returns(bool);
function frameDescriptor(l:$FrameLayout) returns(desc:int);
function frameFieldToSlot(l:$FrameLayout, j:int) returns(int);

var $FrameCounts:[int]int;
var $FrameSlices:[int][int]int;
var $FrameAddrs:[int][int]int;
var $FrameLayouts:[int][int]$FrameLayout;
var $FrameAbss:[int][int][int]int;
var $FrameOffsets:[int][int]int;

function inFrame(layout:$FrameLayout, j:int) returns(bool)
{
  (-frameLayoutLocals(layout)) <= j && j < 2 + frameLayoutArgs(layout)
}

function{:expand false} TVF(l:$FrameLayout) returns(bool) { true }

const ?sectionCount:int;
const ?staticDataPointerBitMap:int;
const ?dataSectionEnd:int;
const ?dataSectionBase:int;

function sectionSlice(ptr:int) returns(section:int);
function sectionBase(section:int) returns(ptr:int) { ro32(?dataSectionBase + 4 * section) }
function sectionEnd(section:int) returns(ptr:int) { ro32(?dataSectionEnd + 4 * section) }
function sectionHasPtr(section:int, j:int) returns(bool);

function inSectionData(ptr:int) returns(bool);

function{:expand false} TVS(s:int, j:int) returns(bool) { true }

const ?callSiteTableCount:int;
const ?codeBaseStartTable:int;
const ?returnAddressToCallSiteSetNumbers:int;
const ?callSiteSetCount:int;
const ?callSiteSetNumberToIndex:int;
const ?activationDescriptorTable:int;

function LookupDesc(t:int, j:int) returns(int)
{
  ro32(ro32(?activationDescriptorTable + 4 * t) + 4 *
    roU16(ro32(?callSiteSetNumberToIndex + 4 * t) + 2 * j))
}

function InTable(t:int, j:int) returns(bool)
{
  0 <= t && t < ?callSiteTableCount && 0 <= j && j < ro32(ro32(?callSiteSetCount + 4 * t))
}

function RetAddrAt(t:int, j:int, retaddr:int) returns(bool)
{
    InTable(t, j)
 && between(ro32(ro32(?returnAddressToCallSiteSetNumbers + 4 * t) + 4 * j),
            ro32(ro32(?returnAddressToCallSiteSetNumbers + 4 * t) + 4 * (j + 1)),
            retaddr - ro32(?codeBaseStartTable + 4 * t))
}

function{:expand false} TVFT(f:int) returns(bool) { true }

function FrameNextInv(f:int, ra:int, nextFp:int, $FrameAddr:[int]int, $FrameLayout:[int]$FrameLayout) returns(bool);
axiom (forall f:int, ra:int, nextFp:int, $FrameAddr:[int]int, $FrameLayout:[int]$FrameLayout::{TVFT(f), FrameNextInv(f, ra, nextFp, $FrameAddr, $FrameLayout)} FrameNextInv(f, ra, nextFp, $FrameAddr, $FrameLayout) ==
(
    f >= 0
 && (f == 0 <==> nextFp == 0)
 && (f > 0 ==>
        $FrameAddr[f - 1] == nextFp
     && (exists t:int, j:int::{TT(t), TO(j)} TT(t) && TO(j) && RetAddrAt(t, j, ra))
     && (forall t:int, j:int::{TT(t), TO(j)} TT(t) && TO(j) ==>
          RetAddrAt(t, j, ra) ==> frameDescriptor($FrameLayout[f - 1]) == LookupDesc(t, j)))
));

function FrameInv(f:int, l:$FrameLayout, $FrameAddr:[int]int, $FrameSlice:[int]int, $FrameLayout:[int]$FrameLayout, $FrameAbs:[int][int]int, $FrameOffset:[int]int) returns(bool)
{
    FrameNextInv(f, $FrameAbs[f][1], $FrameAbs[f][0], $FrameAddr, $FrameLayout)
 && (forall j:int::{TO(j)} TO(j) ==> inFrame(l, j) ==> $FrameSlice[$FrameAddr[f] + 4 * j] == f)
 && (forall j:int::{TO(j)} TO(j) ==> $FrameSlice[$FrameAddr[f] + 4 * j] == f ==>
        word($FrameAddr[f] + 4 * j)
    )
}

function StackInv($FrameCount:int, $FrameAddr:[int]int, $FrameLayout:[int]$FrameLayout,
  $FrameSlice:[int]int, $FrameAbs:[int][int]int, $FrameOffset:[int]int) returns(bool)
{
  (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], $FrameAddr, $FrameSlice, $FrameLayout, $FrameAbs, $FrameOffset))
}

function StackInvS($s:int, $FrameCounts:[int]int, $FrameAddrs:[int][int]int, $FrameLayouts:[int][int]$FrameLayout,
  $FrameSlices:[int][int]int, $FrameAbss:[int][int][int]int, $FrameOffsets:[int][int]int) returns(bool)
{
  StackInv($FrameCounts[$s], $FrameAddrs[$s], $FrameLayouts[$s], $FrameSlices[$s], $FrameAbss[$s], $FrameOffsets[$s])
}

var $SectionMem:[int]int;
var $SectionAbs:[int][int]int;

function SectionInv(s:int, i1:int, i2:int, r:[int]int, $SectionMem:[int]int, $SectionAbs:[int][int]int) returns(bool)
{
  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && i1 + 4 * j < i2 ==>
      sectionSlice(i1 + 4 * j) == s
   && Value(sectionHasPtr(s, j), r, $SectionMem[i1 + 4 * j], $SectionAbs[s][j])
  )
}

function StaticInv(r:[int]int, $SectionMem:[int]int, $SectionAbs:[int][int]int) returns(bool)
{
  (forall s:int::{TV(s)} TV(s) ==> 0 <= s && s < ?sectionCount ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), r, $SectionMem, $SectionAbs))
}

procedure SectionLoad($ptr:int) returns($val:int);
  requires inSectionData($ptr);
  modifies $Eip;
  ensures  word($val);
  ensures  $val == $SectionMem[$ptr];

procedure SectionStore($ptr:int, $val:int);
  requires inSectionData($ptr);
  requires word($val);
  modifies $Eip, $SectionMem;
  ensures  $SectionMem == old($SectionMem)[$ptr := $val];


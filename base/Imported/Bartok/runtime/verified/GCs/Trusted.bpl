//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

/*****************************************************************************
******************************************************************************
**** AXIOMS AND TRUSTED DEFINITIONS
******************************************************************************
*****************************************************************************/

//////////////////////////////////////////////////////////////////////////////
// TRIGGERS
//////////////////////////////////////////////////////////////////////////////

// Triggers for quantifiers
// We could use a single trigger for all values; the distinction between the
// various triggers below is just to help the prover run fast.

// TV is a trigger for values in general, including addresses.
function{:expand false} TV(val:int) returns (bool) { true }

// TO is a trigger specifically for word offsets from addresses, where
// word offset n is byte offset 4 * n.
function{:expand false} TO(wordOffset:int) returns (bool) { true }

// TSlot is a trigger for slots in sparse tags
function{:expand false} TSlot(slot:int) returns (bool) { true }

// TT is a trigger for tables
function{:expand false} TT(table:int) returns (bool) { true }

//////////////////////////////////////////////////////////////////////////////
// WORDS
//////////////////////////////////////////////////////////////////////////////

// i1 <= x < i2
function between(i1:int, i2:int, x:int) returns(bool) { i1 <= x && x < i2 }

// valid 32-bit unsigned words
// word(i) <==> 0 <= i < 2^32
const WORD_HI:int; // 2^32
axiom WORD_HI >= 100; // REVIEW: should we go ahead and set WORD_HI to exactly 2^32?
function word(val:int) returns(bool) { 0 <= val && val < WORD_HI }

// converts 2's complement 32-bit val into signed integer
function asSigned(val:int) returns(int);

// null value(s)
const NULL: int; axiom NULL == 0;

//////////////////////////////////////////////////////////////////////////////
// ASSEMBLY LANGUAGE
//////////////////////////////////////////////////////////////////////////////

// invariant: word(r) for each register r
// To maintain invariant, simply check word(exp) for each assignment r := exp

// invariant: word(r) for each word w in memory
// To maintain invariant, simply check word(exp) for each store of exp to memory

var eax:int;
var ebx:int;
var ecx:int;
var edx:int;
var esi:int;
var edi:int;
var ebp:int;
var esp:int;

function neg (int) returns (int);
function and (int, int) returns (int);
function or (int, int) returns (int);
function xor (int, int) returns (int);
function shl (int, int) returns (int);
function shr (int, int) returns (int);

function{:expand false} TVM(a:int, b:int) returns(bool) { true }
function Mult(a:int, b:int) returns(int);
axiom (forall a:int, b:int::{TVM(a, b)} Mult(a, b) == a * b);

// REVIEW: one would hope that this axiom is derivable from
// Mult(a, b) == a * b, using b = b1 + b2, but Z3 couldn't seem to do it yet:
function{:expand false} TVM3(a:int, b1:int, b2:int) returns(bool) { true }
axiom (forall a:int, b1:int, b2:int::{TVM3(a, b1, b2)} Mult(a, b1 + b2) == a * (b1 + b2));

procedure Add(x:int, y:int) returns(ret:int);
  requires word(x + y);
  ensures  ret == x + y;

procedure Sub(x:int, y:int) returns(ret:int);
  requires word(x - y);
  ensures  ret == x - y;

procedure Mul(x:int, y:int) returns(ret:int, hi:int);
  requires word(x * y);
  ensures  ret == x * y;
  ensures  ret == Mult(x, y);

// Note: we only support 32-bit division, so the upper 32 bits must be 0
procedure Div(x:int, zero:int, y:int) returns(ret:int, rem:int);
  requires zero == 0;
  requires y != 0;
  ensures  word(ret);
  ensures  word(rem);
  ensures  ret == x / y && ret * y + rem == x;
  ensures  rem == x % y && rem < y;

procedure Not(x:int) returns(ret:int);
  ensures  ret == neg(x);
  ensures  word(ret);

procedure And(x1:int, x2:int) returns(ret:int);
  ensures  ret == and(x1, x2);
  ensures  word(ret);

procedure Or(x1:int, x2:int) returns(ret:int);
  ensures  ret == or(x1, x2);
  ensures  word(ret);

procedure Xor(x1:int, x2:int) returns(ret:int);
  ensures  ret == xor(x1, x2);
  ensures  word(ret);

procedure Shl(x1:int, x2:int) returns(ret:int);
  requires x2 < 32;
  ensures  ret == shl(x1, x2);
  ensures  word(ret);

procedure Shr(x1:int, x2:int) returns(ret:int);
  requires x2 < 32;
  ensures  ret == shr(x1, x2);
  ensures  word(ret);

// run-time overflow checked
procedure AddChecked(x:int, y:int) returns(ret:int);
  ensures  word(x + y);
  ensures  ret == x + y;

// run-time overflow checked
procedure SubChecked(x:int, y:int) returns(ret:int);
  ensures  word(x - y);
  ensures  ret == x - y;

// run-time overflow checked
procedure MulChecked(x:int, y:int) returns(ret:int, hi:int);
  ensures  word(x * y);
  ensures  word(Mult(x, y));
  ensures  ret == x * y;
  ensures  ret == Mult(x, y);

procedure Lea(addr:int) returns(ret:int);
  requires word(addr);
  ensures  ret == addr;

procedure LeaUnchecked(addr:int) returns(ret:int);
  ensures  word(ret);

// REVIEW: add more general support for signed arithmetic?
procedure LeaSignedIndex(base:int, scale:int, index:int, offset:int) returns(ret:int);
  requires scale == 1 || scale == 2 || scale == 4 || scale == 8;
  requires word(base + scale * asSigned(index) + offset);
  ensures  ret == base + scale * asSigned(index) + offset;

procedure DebugBreak();
  ensures false; // DebugBreak never returns.

//////////////////////////////////////////////////////////////////////////////
// READ-ONLY MEMORY
//////////////////////////////////////////////////////////////////////////////

function roS8(ptr:int) returns(int);
function roU8(ptr:int) returns(int);
function roS16(ptr:int) returns(int);
function roU16(ptr:int) returns(int);
function ro32(ptr:int) returns(int);

function inRo(ptr:int, size:int) returns(bool);

// read and zero-extend 8 bits
procedure RoLoadU8(ptr:int) returns (val:int);
  requires inRo(ptr, 1);
  ensures  word(val);
  ensures  val == roU8(ptr);

// read and sign-extend 8 bits
procedure RoLoadS8(ptr:int) returns (val:int);
  requires inRo(ptr, 1);
  ensures  word(val);
  ensures  asSigned(val) == roS8(ptr);

// read and zero-extend 16 bits
procedure RoLoadU16(ptr:int) returns (val:int);
  requires inRo(ptr, 2);
  ensures  word(val);
  ensures  val == roU16(ptr);

// read and sign-extend 16 bits
procedure RoLoadS16(ptr:int) returns (val:int);
  requires inRo(ptr, 2);
  ensures  word(val);
  ensures  asSigned(val) == roS16(ptr);

procedure RoLoad32(ptr:int) returns (val:int);
  requires inRo(ptr, 4);
  ensures  word(val);
  ensures  val == ro32(ptr);

//////////////////////////////////////////////////////////////////////////////
// GC-CONTROLLED MEMORY
//////////////////////////////////////////////////////////////////////////////

// valid gc-controlled addresses (must be disjoint from null values)
// warning: because of interior pointers, ?gcHi must be a 32-bit word
//   (it can equal 2^32 - 1, but not 2^32)
const ?gcLo: int;
const ?gcHi: int;
axiom NULL < ?gcLo;
axiom ?gcLo <= ?gcHi;
axiom ?gcHi < WORD_HI;
function gcAddr(i:int) returns (bool) {?gcLo <= i && i < ?gcHi}
function gcAddrEx(i:int) returns (bool) {?gcLo <= i && i <= ?gcHi}

// Aligned(i) <==> i is a multiple of 4
function Aligned(i:int) returns(bool);
axiom (forall i:int, j:int::{TV(i), TO(j)} TV(i) && TO(j) ==> Aligned(i) == Aligned(i + 4 * j));
axiom Aligned(?gcLo);
axiom Aligned(?gcHi);

// $GcMem[i] = data at address i, if gcAddr(i) and Aligned(i).
var $GcMem:[int]int; // Do not modify directly! Use procedures below.

// Read a word from gc-controlled memory
procedure GcLoad(ptr:int) returns (val:int);
  requires TV(ptr);
  requires gcAddr(ptr);
  requires Aligned(ptr);
  ensures  word(val);
  ensures  TV(val);
  ensures  val == $GcMem[ptr];

// Write a word to gc-controlled memory
procedure GcStore(ptr:int, val:int);
  requires gcAddr(ptr);
  requires Aligned(ptr);
  requires word(val);
  requires TV(ptr) && TV(val);
  modifies $GcMem;
  ensures  $GcMem == old($GcMem)[ptr := val];

// MAP_ZERO maps all addresses to value zero.
const MAP_ZERO:[int]int;
axiom (forall i:int::{TV(i)} TV(i) ==> MAP_ZERO[i] == 0);

//////////////////////////////////////////////////////////////////////////////
// ABSTRACT NODES
//////////////////////////////////////////////////////////////////////////////

// The mutator controls an abstract graph consisting of abstract nodes,
// which contain abstract values.  These abstract values may be
// abstract primitive values or abstract edges pointing to abstract nodes.

// Abstract values are represented by integers.  For any integer A,
// we may interpret A as an abstract primitive value or an abstract pointer:
//   - the abstract primitive value A represents the concrete integer A
//   - the abstract pointer A may be one of the following:
//     - NO_ABS, representing no value (used for partial maps)
//     - any other value, representing a node in the abstract graph
// Any primitive value A will satisfy word(A). To avoid confusion
// between abstract primitive and abstract pointer values, the
// mutator should choose abstract pointer values A such that !word(A).

const NO_ABS:int; // the value "none"

// Each abstract object node A has some number of fields,
// which is chosen when A is allocated, and never changes afterwards.
function numFields(abs:int) returns (int);

// $AbsMem represents of the abstract graph's edges: for abstract node A
// and field j, $AbsMem[A][j] is the abstract node pointed to by A's field j.
// Do not modify $AbsMem directly!  $AbsMem is controlled by the mutator.
var $AbsMem:[int][int]int;

//////////////////////////////////////////////////////////////////////////////
// REACHABILITY
//////////////////////////////////////////////////////////////////////////////

type Time;
var $Time:Time;

// reached(A,T) means that the GC has reached abstract node A at some time
// after the initial time T.  Initially (at time T), the mutator will
// say that reached(root, T).  After that, the GC calls the "reach"
// ghost procedure to generate reached(A, T) for other A.
function reached(a:int, t:Time) returns (bool);

// If we've reached A, and A points to A', then reach A'.
// Note: this depends on $AbsMem being defined by the mutator.  The GC
// should not write to $AbsMem directly (if it did, then it could reach
// anything, trivially).
procedure reach($a:int, $j:int, $t:Time);
  requires reached($a, $t);
  requires $AbsMem[$a][$j] != NO_ABS;
  ensures  reached($AbsMem[$a][$j], $t);

//////////////////////////////////////////////////////////////////////////////
// POINTERS AND VALUES
//////////////////////////////////////////////////////////////////////////////

function Pointer(rev:[int]int, ptr:int, abs:int) returns (bool)
{
  gcAddr(ptr) && Aligned(ptr) && abs != NO_ABS && rev[ptr] == abs // AbsMapped(ptr,rev,abs)
}

// An interior pointer ("interiorPtr") points to an actual
// object address ("ptr") plus some offset ("offset"):
//   !nullAddr(interiorPtr) ==> interiorPtr == ptr + offset && 0 <= offset && offset <= 4 * numFields($toAbs[ptr - 4]) - 4;
function InteriorValue(isPtr:bool, rev:[int]int, val:int, abs:int, offset:int) returns (bool)
{
     (isPtr && word(val) && gcAddrEx(val) && Pointer(rev, val - 4 - offset, abs)
       && !word(abs)
       && 0 <= offset && offset <= 4 * numFields(abs) - 4)
  || (isPtr && word(val) && !gcAddrEx(val) && abs == val)
  || (!isPtr && word(val) && abs == val)
}

function Value(isPtr:bool, rev:[int]int, val:int, abs:int) returns (bool)
{
  InteriorValue(isPtr, rev, val, abs, 0)
}

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
axiom (forall abs:int, vt:int::{TVT(abs, vt)} VTable(abs, vt) <==>
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

axiom (forall abs:int, vt:int::{TVT(abs, vt)} VTable(abs, vt) ==>
    inRo(vt + ?VT_MASK, 4)
 && inRo(vt + ?VT_BASE_LENGTH, 4)
 && inRo(vt + ?VT_ARRAY_ELEMENT_SIZE, 4)
 && inRo(vt + ?VT_ARRAY_ELEMENT_CLASS, 4)
 && inRo(vt + ?VT_ARRAY_OF, 4)
);

function pad(i:int) returns(int)
{
  and(i + 3, neg(3))
}

function{:expand false} TVL(abs:int) returns(bool) { true }
function ObjSize(abs:int, vt:int, nElems1:int, nElems2:int) returns(bool);
axiom (forall abs:int, vt:int, nElems1:int, nElems2:int::{TVL(abs), ObjSize(abs, vt, nElems1, nElems2)} ObjSize(abs, vt, nElems1, nElems2) <==>
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
function frameLayoutArgs($FrameLayout) returns(int);
function frameLayoutLocals($FrameLayout) returns(int);
function frameHasPtr($FrameLayout, int) returns(bool);
function frameDescriptor($FrameLayout) returns(desc:int);
function frameFieldToSlot($FrameLayout, int) returns(int);

var $FrameCount:int;
var $FrameSlice:[int]int;
var $FrameAddr:[int]int;
var $FrameLayout:[int]$FrameLayout;
var $FrameMem:[int]int;
var $FrameAbs:[int][int]int;
var $FrameOffset:[int]int;

function inFrame(layout:$FrameLayout, j:int) returns(bool)
{
  -frameLayoutLocals(layout) <= j && j < 2 + frameLayoutArgs(layout)
}

function{:expand false} TVF(l:$FrameLayout) returns(bool) { true }
axiom (forall l:$FrameLayout, j:int::{TVF(l),TO(j)}
    (inFrame(l, 0) && !frameHasPtr(l, 0))
 && (inFrame(l, 1) && !frameHasPtr(l, 1))
 && (TO(j) && frameHasPtr(l, j) ==> inFrame(l, j))
 && (TO(j) && getBit(frameDescriptor(l), 0) && !getBit(frameDescriptor(l), 1) && and(shr(frameDescriptor(l), 6), 1023) == 0 ==>
        between(0, 16, frameLayoutArgs(l))
     && frameLayoutArgs(l) == and(shr(frameDescriptor(l), 2), 15)
     && (frameHasPtr(l, j) ==> 0 <= frameLayoutArgs(l) + 1 - j && frameLayoutArgs(l) - 1 - j < 16)
     && (0 <= frameLayoutArgs(l) + 1 - j && frameLayoutArgs(l) - 1 - j < 16 ==> (
            (j >= 2 ==> frameHasPtr(l, j) == getBit(frameDescriptor(l), 16 + frameLayoutArgs(l) + 1 - j))
         && (j < 0  ==> frameHasPtr(l, j) == getBit(frameDescriptor(l), 16 + frameLayoutArgs(l) - 1 - j)))
    ))
 && (TO(j) && !getBit(frameDescriptor(l), 0) ==> inRo(frameDescriptor(l), 4))
 && (TO(j) && !getBit(frameDescriptor(l), 0) && ro32(frameDescriptor(l)) == 4096 && inFrame(l, j) ==> (
        inRo(frameDescriptor(l) + 4, 1)
     && inRo(frameDescriptor(l) + 6 + frameFieldToSlot(l, j), 1)
     && j == roS8(frameDescriptor(l) + 6 + frameFieldToSlot(l, j))
     && frameHasPtr(l, j) == (
          between(0, roU8(frameDescriptor(l) + 4), frameFieldToSlot(l, j))
        )
    )));
axiom (forall l:$FrameLayout, k:int::{TVF(l),TSlot(k)}
        TSlot(k) && !getBit(frameDescriptor(l), 0) && ro32(frameDescriptor(l)) == 4096 && between(0, roU8(frameDescriptor(l) + 4), k) ==>
            inFrame(l, roS8(frameDescriptor(l) + 6 + k))
         && k == frameFieldToSlot(l, roS8(frameDescriptor(l) + 6 + k))
    );

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
axiom (forall s:int, j:int::{TVS(s, j)}
        0 <= s && s < ?sectionCount && 0 <= j ==>
            inRo(?dataSectionBase + 4 * s, 4)
         && inRo(?dataSectionEnd + 4 * s, 4)
         && inRo(?staticDataPointerBitMap + 4 * s, 4)
         && (sectionBase(s) + 4 * j < sectionEnd(s) ==>
                inSectionData(ro32(?dataSectionBase + 4 * s) + 4 * j)
             && inRo(ro32(?staticDataPointerBitMap + 4 * s) + 4 * shr(j, 5), 4)
             && and(j, 31) < 32 // REVIEW: this is true, so just prove it
             && sectionHasPtr(s, j) == getBit(
                  ro32(ro32(?staticDataPointerBitMap + 4 * s) + 4 * shr(j, 5)),
                  and(j, 31)
                  )));

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
axiom (forall f:int, ra:int, nextFp:int, $FrameAddr:[int]int, $FrameLayout:[int]$FrameLayout::{TVFT(f), FrameNextInv(f, ra, nextFp, $FrameAddr, $FrameLayout)} FrameNextInv(f, ra, nextFp, $FrameAddr, $FrameLayout) <==>
(
    f >= 0
 && (f == 0 <==> !(exists t:int, j:int::{TT(t), TO(j)} TT(t) && TO(j) && RetAddrAt(t, j, ra)))
 && (f > 0 ==>
        $FrameAddr[f - 1] == nextFp
     && (forall t:int, j:int::{TT(t), TO(j)} TT(t) && TO(j) ==>
          RetAddrAt(t, j, ra) ==> frameDescriptor($FrameLayout[f - 1]) == LookupDesc(t, j)))
));

axiom (forall f:int::{TVFT(f)}
(
  (forall t:int::{TT(t)} TT(t) ==> 0 <= t && t < ?callSiteTableCount ==>
      inRo(?codeBaseStartTable + 4 * t, 4)
   && inRo(?returnAddressToCallSiteSetNumbers + 4 * t, 4)
   && inRo(?callSiteSetCount + 4 * t, 4)
   && inRo(ro32(?callSiteSetCount + 4 * t), 4)
   && inRo(?callSiteSetNumberToIndex + 4 * t, 4)
   && inRo(?activationDescriptorTable + 4 * t, 4)
   && (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j <= ro32(ro32(?callSiteSetCount + 4 * t)) ==>
          inRo(ro32(?returnAddressToCallSiteSetNumbers + 4 * t) + 4 * j, 4)
       && inRo(ro32(?callSiteSetNumberToIndex + 4 * t) + 2 * j, 2)
       && inRo(ro32(?activationDescriptorTable + 4 * t)
            + 4 * roU16(ro32(?callSiteSetNumberToIndex + 4 * t) + 2 * j), 4)
      )
  )
));

axiom (forall f:int::{TVFT(f)}
(
  (forall t:int, j1:int, j2:int::{TT(t), TO(j1), TO(j2)} TT(t) && TO(j1) && TO(j2) ==>
    0 <= t && t < ?callSiteTableCount && 0 <= j1 && j1 < j2 && j2 <= ro32(ro32(?callSiteSetCount + 4 * t)) ==>
      ro32(ro32(?returnAddressToCallSiteSetNumbers + 4 * t) + 4 * j1) < ro32(ro32(?returnAddressToCallSiteSetNumbers + 4 * t) + 4 * j2)
  )
));

// Note: we allow reads, but not writes, from $frame == $FrameCount, which
// is the garbage collector's own initial stack frame.  This feature allows
// the collector to read the arguments and saved return address set
// by the mutator.  It does not allow reading the collector's own data.
procedure FrameLoad($frame:int, ptr:int) returns(val:int);
  requires 0 <= $frame && $frame <= $FrameCount;
  requires $FrameSlice[ptr] == $frame;
  ensures  word(val);
  ensures  val == $FrameMem[ptr];

procedure FrameStore($frame:int, ptr:int, val:int);
  requires 0 <= $frame && $frame < $FrameCount;
  requires $FrameSlice[ptr] == $frame;
  requires word(val);
  modifies $FrameMem;
  ensures  $FrameMem == old($FrameMem)[ptr := val];

function FrameInv(f:int, l:$FrameLayout, r:[int]int, $FrameAddr:[int]int, $FrameSlice:[int]int, $FrameLayout:[int]$FrameLayout, $FrameMem:[int]int, $FrameAbs:[int][int]int, $FrameOffset:[int]int, $Time:Time) returns(bool)
{
    FrameNextInv(f, $FrameMem[$FrameAddr[f] + 4], $FrameMem[$FrameAddr[f]], $FrameAddr, $FrameLayout)
 && (forall j:int::{TO(j)} TO(j) ==> inFrame(l, j) ==>
        $FrameSlice[$FrameAddr[f] + 4 * j] == f
     && word($FrameAddr[f] + 4 * j)
     && InteriorValue(frameHasPtr(l, j), r, $FrameMem[$FrameAddr[f] + 4 * j], $FrameAbs[f][j], $FrameOffset[$FrameAddr[f] + 4 * j])
     && (frameHasPtr(l, j) && gcAddrEx($FrameMem[$FrameAddr[f] + 4 * j]) ==> reached($FrameAbs[f][j], $Time))
    )
}

function StackInv(r:[int]int, $FrameCount:int, $FrameAddr:[int]int, $FrameLayout:[int]$FrameLayout,
  $FrameSlice:[int]int, $FrameMem:[int]int, $FrameAbs:[int][int]int, $FrameOffset:[int]int, t:Time) returns(bool)
{
  (forall f:int::{TV(f)} TV(f) ==> 0 <= f && f < $FrameCount ==>
    FrameInv(f, $FrameLayout[f], r, $FrameAddr, $FrameSlice, $FrameLayout, $FrameMem, $FrameAbs, $FrameOffset, t))
}

var $SectionMem:[int]int;
var $SectionAbs:[int][int]int;

function SectionInv(s:int, i1:int, i2:int, r:[int]int, $SectionMem:[int]int, $SectionAbs:[int][int]int, t:Time) returns(bool)
{
  (forall j:int::{TO(j)} TO(j) ==> 0 <= j && i1 + 4 * j < i2 ==>
      sectionSlice(i1 + 4 * j) == s
   && Value(sectionHasPtr(s, j), r, $SectionMem[i1 + 4 * j], $SectionAbs[s][j])
   && (sectionHasPtr(s, j) && gcAddrEx($SectionMem[i1 + 4 * j]) ==> reached($SectionAbs[s][j], t))
  )
}

function StaticInv(r:[int]int, $SectionMem:[int]int, $SectionAbs:[int][int]int, t:Time) returns(bool)
{
  (forall s:int::{TV(s)} TV(s) ==> 0 <= s && s < ?sectionCount ==>
    SectionInv(s, sectionBase(s), sectionEnd(s), r, $SectionMem, $SectionAbs, t))
}

procedure SectionLoad(ptr:int) returns(val:int);
  requires inSectionData(ptr);
  ensures  word(val);
  ensures  val == $SectionMem[ptr];

procedure SectionStore(ptr:int, val:int);
  requires inSectionData(ptr);
  requires word(val);
  modifies $SectionMem;
  ensures  $SectionMem == old($SectionMem)[ptr := val];

//////////////////////////////////////////////////////////////////////////////
// ABSTRACT AND CONCRETE GRAPHS
//////////////////////////////////////////////////////////////////////////////

// Each integer i is considered a concrete node.
// The memory manager controls concrete nodes in memory.  
//   - Each abstract object node is either mapped to one concrete node or is unmapped
//   - Each concrete node is either mapped to one abstract object node or is unmapped
//   - If abstract object node A is mapped to concrete node C, then C is mapped to A
// Let the notation C<-->A indicate that A is mapped to C and C is mapped to A.
// Let the notation C-->none indicate that C is unmapped.
// Let the notation A-->none indicate that A is unmapped.

// The variable $toAbs maps concrete nodes to abstract nodes, and thereby
// exactly describes all C<-->A and C-->none.  The A-->none mappings are
// implied; if there is no C such that C<-->A, then A-->none.
var $toAbs:[int]int; // maps a concrete node C to an abstract node A or to "none"

// MAP_NO_ABS has no C<-->A mappings.
const MAP_NO_ABS:[int]int;
axiom (forall i:int::{TV(i)} TV(i) ==> MAP_NO_ABS[i] == NO_ABS);

// WellFormed($toAbs) ensures that if C1 != C2 and $toAbs[C1] != NO_ABS
// and $toAbs[C2] != NO_ABS then $toAbs[C1] != $toAbs[C2].
function WellFormed($toAbs:[int]int) returns(bool)
{
    (forall i1:int, i2:int::{TV(i1), TV(i2)} TV(i1) && TV(i2)
      && gcAddr(i1) && gcAddr(i2) && i1 != i2 && $toAbs[i1] != NO_ABS && $toAbs[i2] != NO_ABS
      ==> $toAbs[i1] != $toAbs[i2])
}


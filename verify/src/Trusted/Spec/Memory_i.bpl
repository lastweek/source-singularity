//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

//////////////////////////////////////////////////////////////////////////////
// MEMORY ADDRESSES
//////////////////////////////////////////////////////////////////////////////

// Aligned(i) <==> i is a multiple of 4
function Aligned(i:int) returns(bool);

//////////////////////////////////////////////////////////////////////////////
// MAIN MEMORY
//////////////////////////////////////////////////////////////////////////////

const ?memLo: int;
const ?memHi: int;
function memAddr(i:int) returns (bool) {?memLo <= i && i < ?memHi}
function memAddrEx(i:int) returns (bool) {?memLo <= i && i <= ?memHi}

// $Mem[i] = data at address i, if memAddr(i) and Aligned(i).
var $Mem:[int]int; // Do not modify directly! Use Load and Store.

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
procedure RoLoadU8($ptr:int) returns ($val:int);
  requires inRo($ptr, 1);
  modifies $Eip;
  ensures  word($val);
  ensures  $val == roU8($ptr);

// read and sign-extend 8 bits
procedure RoLoadS8($ptr:int) returns ($val:int);
  requires inRo($ptr, 1);
  modifies $Eip;
  ensures  word($val);
  ensures  asSigned($val) == roS8($ptr);

// read and zero-extend 16 bits
procedure RoLoadU16($ptr:int) returns ($val:int);
  requires inRo($ptr, 2);
  modifies $Eip;
  ensures  word($val);
  ensures  $val == roU16($ptr);

// read and sign-extend 16 bits
procedure RoLoadS16($ptr:int) returns ($val:int);
  requires inRo($ptr, 2);
  modifies $Eip;
  ensures  word($val);
  ensures  asSigned($val) == roS16($ptr);

procedure RoLoad32($ptr:int) returns ($val:int);
  requires inRo($ptr, 4);
  modifies $Eip;
  ensures  word($val);
  ensures  $val == ro32($ptr);

//////////////////////////////////////////////////////////////////////////////
// GC-CONTROLLED MEMORY
//////////////////////////////////////////////////////////////////////////////

// valid gc-controlled addresses (must be disjoint from null values)
// warning: because of interior pointers, ?gcHi must be a 32-bit word
//   (it can equal 2^32 - 1, but not 2^32)
const ?gcLo: int; axiom ?gcLo == ?memLo + 1114112 + 8 * 65536;
const ?gcHi: int; axiom ?gcHi == ?memHi;
function gcAddr(i:int) returns (bool) {?gcLo <= i && i < ?gcHi}
function gcAddrEx(i:int) returns (bool) {?gcLo <= i && i <= ?gcHi}

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

// WellFormed($toAbs) ensures that if C1 != C2 and $toAbs[C1] != NO_ABS
// and $toAbs[C2] != NO_ABS then $toAbs[C1] != $toAbs[C2].
function WellFormed($toAbs:[int]int) returns(bool)
{
    (forall i1:int, i2:int::{TV(i1), TV(i2)} TV(i1) && TV(i2)
      && gcAddr(i1) && gcAddr(i2) && i1 != i2 && $toAbs[i1] != NO_ABS && $toAbs[i2] != NO_ABS
      ==> $toAbs[i1] != $toAbs[i2])
}


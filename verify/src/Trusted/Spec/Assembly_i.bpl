//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

//////////////////////////////////////////////////////////////////////////////
// ASSEMBLY LANGUAGE
//////////////////////////////////////////////////////////////////////////////

// Where must the called procedure return to?
type ReturnTo;
var $RET:ReturnTo; // called procedure must return to old($RET)
// Return to return address $eip via "ret" instruction
function ReturnToAddr($eip:int) returns(ReturnTo);
// Return to stack (eip, cs, eflags, ...) at $esp
function ReturnToInterrupted($eip:int, $cs:int, $efl:int) returns(ReturnTo);

// invariant: word(r) for each register r
// To maintain invariant, simply check word(exp) for each assignment r := exp

// invariant: word(r) for each word w in memory
// To maintain invariant, simply check word(exp) for each store of exp to memory

procedure Mov($x:int) returns($ret:int);
  modifies $Eip;
  ensures  $ret == $x;

procedure Add($x:int, $y:int) returns($ret:int);
  requires word($x + $y);
  modifies $Eip;
  ensures  $ret == $x + $y;

procedure Sub($x:int, $y:int) returns($ret:int);
  requires word($x - $y);
  modifies $Eip;
  ensures  $ret == $x - $y;

procedure Mul($x:int, $y:int) returns($ret:int, $hi:int);
  requires word($x * $y);
  modifies $Eip;
  ensures  $ret == $x * $y;
  ensures  $ret == Mult($x, $y);

// Note: we only support 32-bit division, so the upper 32 bits must be 0
procedure Div($x:int, $zero:int, $y:int) returns($ret:int, $rem:int);
  requires $zero == 0;
  requires $y != 0;
  modifies $Eip;
  ensures  word($ret);
  ensures  word($rem);
  ensures  $ret == $x / $y && $ret * $y + $rem == $x;
  ensures  $rem == $x % $y && $rem < $y;

procedure Not($x:int) returns($ret:int);
  modifies $Eip;
  ensures  $ret == neg($x);
  ensures  word($ret);

procedure And($x1:int, $x2:int) returns($ret:int);
  modifies $Eip;
  ensures  $ret == and($x1, $x2);
  ensures  word($ret);

procedure Or($x1:int, $x2:int) returns($ret:int);
  modifies $Eip;
  ensures  $ret == or($x1, $x2);
  ensures  word($ret);

procedure Xor($x1:int, $x2:int) returns($ret:int);
  modifies $Eip;
  ensures  $ret == xor($x1, $x2);
  ensures  word($ret);

procedure Shl($x1:int, $x2:int) returns($ret:int);
  requires $x2 < 32;
  modifies $Eip;
  ensures  $ret == shl($x1, $x2);
  ensures  word($ret);

procedure Shr($x1:int, $x2:int) returns($ret:int);
  requires $x2 < 32;
  modifies $Eip;
  ensures  $ret == shr($x1, $x2);
  ensures  word($ret);

// run-time overflow checked
procedure AddChecked($x:int, $y:int) returns($ret:int);
  modifies $Eip;
  ensures  word($x + $y);
  ensures  $ret == $x + $y;

// run-time overflow checked
procedure SubChecked($x:int, $y:int) returns($ret:int);
  modifies $Eip;
  ensures  word($x - $y);
  ensures  $ret == $x - $y;

// run-time overflow checked
procedure MulChecked($x:int, $y:int) returns($ret:int, $hi:int);
  modifies $Eip;
  ensures  word($x * $y);
  ensures  word(Mult($x, $y));
  ensures  $ret == $x * $y;
  ensures  $ret == Mult($x, $y);

procedure Lea($addr:int) returns($ret:int);
  requires word($addr);
  modifies $Eip;
  ensures  $ret == $addr;

procedure LeaUnchecked($addr:int) returns($ret:int);
  modifies $Eip;
  ensures  word($ret);

// REVIEW: add more general support for signed arithmetic?
procedure LeaSignedIndex($base:int, $scale:int, $index:int, $offset:int) returns($ret:int);
  requires $scale == 1 || $scale == 2 || $scale == 4 || $scale == 8;
  requires word($base + $scale * asSigned($index) + $offset);
  modifies $Eip;
  ensures  $ret == $base + $scale * asSigned($index) + $offset;

// Read a word from memory
procedure Load($ptr:int) returns ($val:int);
  requires memAddr($ptr);
  requires Aligned($ptr);
  modifies $Eip;
  ensures  word($val);
  ensures  $val == $Mem[$ptr];

// Write a word to memory
procedure Store($ptr:int, $val:int);
  requires memAddr($ptr);
  requires Aligned($ptr);
  requires word($val);
  modifies $Eip, $Mem;
  ensures  $Mem == old($Mem)[$ptr := $val];

// Where is the instruction that follows $Eip?
// (This equals $Eip + sizeof(instruction at $Eip).)
function NextEip($Eip:int) returns(int);

// A call instruction consists of a call to Call, which models
// pushing the return address, followed by the Boogie call to the procedure.
// Example:
//   call Call(); call Foo(...);
procedure Call();
  requires memAddr(esp - 4);
  requires Aligned(esp);
  modifies $Eip, esp, $Mem, $RET;
  ensures  esp == old(esp) - 4;
  ensures  Aligned(esp);
  ensures  $RET == ReturnToAddr(NextEip(old($Eip)));
  ensures  $Mem == old($Mem)[esp := NextEip(old($Eip))];

// A return instruction consists of a call to Ret, which models
// popping the return address, followed a Boogie return.
// Ret requires that the procedure returns to whoever called it
// (i.e. call/return is last-in, first-out).  It does not
// require that the stack pointer be the same as before.
// Example:
//   call Ret(old($RET)); return;
procedure Ret($oldRA:ReturnTo);
  requires ReturnToAddr($Mem[esp]) == $oldRA;
  requires Aligned(esp);
  modifies $Eip, esp;
  ensures  esp == old(esp) + 4;
  ensures  Aligned(esp);

// An iret instruction consists of a call to IRet, which
// models popping the 3 words eip, cs, eflags.
// Example:
//   call IRet(old($RET)); return;
procedure IRet($oldRA:ReturnTo);
  requires ReturnToInterrupted($Mem[esp], $Mem[esp + 4], $Mem[esp + 8]) == $oldRA;
  requires Aligned(esp);
  modifies $Eip, esp;
  ensures  esp == old(esp) + 12;
  ensures  Aligned(esp);

// Example:
//   call Go(); goto foo;
//   call Go(); if(...) { goto foo; }
procedure Go();
  modifies $Eip;

// Read time-stamp counter (cycle counter)
procedure Rdtsc();
  modifies $Eip, eax, edx;

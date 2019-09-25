//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

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

//////////////////////////////////////////////////////////////////////////////
// WORDS
//////////////////////////////////////////////////////////////////////////////

// i1 <= x < i2
function between(i1:int, i2:int, x:int) returns(bool) { i1 <= x && x < i2 }

// valid 32-bit unsigned words
// word(i) <==> 0 <= i < 2^32
const WORD_HI:int; // 2^32
function word(val:int) returns(bool) { 0 <= val && val < WORD_HI }

// converts 2's complement 32-bit val into signed integer
function asSigned(val:int) returns(int);

function neg (x:int) returns (int);
function and (x:int, y:int) returns (int);
function or  (x:int, y:int) returns (int);
function xor (x:int, y:int) returns (int);
function shl (x:int, y:int) returns (int);
function shr (x:int, y:int) returns (int);

// null value(s)
const NULL: int; axiom NULL == 0;

function{:expand false} TVM(a:int, b:int) returns(bool) { true }
function Mult(a:int, b:int) returns(int);
axiom (forall a:int, b:int::{TVM(a, b)} Mult(a, b) == a * b);

function{:expand false} TVM3(a:int, b1:int, b2:int) returns(bool) { true }


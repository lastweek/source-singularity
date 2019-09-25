//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// Axioms about bit vectors, *not* enabling built-in Z3 support for bit vectors.  

// Note: the "/bv:z" option must still be used, because the type "bv32" appears
// below.  However, because the ":bvbuiltin" flag is omitted from the
// declarations below, Z3 will treat "$add", "$sub" as uninterpreted functions
// rather than bit vector operations.  This is needed for efficiency.

// Imports:
//   - Trusted.bpl

axiom WORD_HI == 2147483647 + 2147483647 + 2;

function $add(x:bv32, y:bv32) returns(bv32);
function $sub(x:bv32, y:bv32) returns(bv32);
function $mul(x:bv32, y:bv32) returns(bv32);
function $and(x:bv32, y:bv32) returns(bv32);
function $or(x:bv32, y:bv32) returns(bv32);
function $shr(x:bv32, y:bv32) returns(bv32);
function $shl(x:bv32, y:bv32) returns(bv32);
function $not(x:bv32) returns(bv32);
function $le(x:bv32, y:bv32) returns(bool);

function{:expand false} TBV(b:bv32) returns(bool) { true }

// meaning undefined if !word(i)
function B(i:int) returns(bv32);
function I(b:bv32) returns(int);

axiom I(1bv32) == 1;

axiom (forall i1:int, i2:int::{B(i1),B(i2)} word(i1) && word(i2) ==> (i1 == i2 <==> B(i1) == B(i2)));
axiom (forall b1:bv32, b2:bv32::{I(b1),I(b2)} b1 == b2 <==> I(b1) == I(b2));

axiom (forall b:bv32::{I(b)} word(I(b)));
axiom (forall b:bv32::{B(I(b))} B(I(b)) == b);
axiom (forall i:int::{I(B(i))} word(i) ==> I(B(i)) == i);

axiom (forall b1:bv32, b2:bv32::{$add(b1, b2)}{TBV(b1),TBV(b2)} word(I(b1) + I(b2)) ==> I(b1) + I(b2) == I($add(b1, b2)));
axiom (forall b1:bv32, b2:bv32::{$sub(b1, b2)}{TBV(b1),TBV(b2)} word(I(b1) - I(b2)) ==> I(b1) - I(b2) == I($sub(b1, b2)));
axiom (forall b1:bv32, b2:bv32::{$mul(b1, b2)}{TBV(b1),TBV(b2)} word(I(b1) * I(b2)) ==> I(b1) * I(b2) == I($mul(b1, b2)));
axiom (forall b1:bv32, b2:bv32::{$le(b1, b2)}{TBV(b1),TBV(b2)} I(b1) <= I(b2) <==> $le(b1, b2));
axiom (forall i1:int, i2:int::{and(i1, i2)}  and(i1, i2) == I($and(B(i1), B(i2))) );
axiom (forall i1:int, i2:int::{or(i1, i2)}  or(i1, i2) == I($or(B(i1), B(i2))) );
axiom (forall i1:int, i2:int::{shl(i1, i2)}  shl(i1, i2) == I($shl(B(i1), B(i2))) );
axiom (forall i1:int, i2:int::{shr(i1, i2)}  shr(i1, i2) == I($shr(B(i1), B(i2))) );
axiom (forall i:int::{neg(i)} neg(i) == I($not(B(i))));

axiom (forall b:bv32::{Aligned(I(b))} Aligned(I(b)) == ($and(b, 3bv32) == 0bv32));


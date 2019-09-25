//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// Axioms about bit vectors, using built-in Z3 support for bit vectors

function {:bvbuiltin "bvadd"} $add(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $sub(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $mul(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvand"} $and(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvor"} $or(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $shr(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $shl(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvnot"} $not(x:bv32) returns(bv32);
function {:bvbuiltin "bvule"} $le(x:bv32, y:bv32) returns(bool);

function{:expand false} TV(i:int) returns(bool) { true }
function{:expand false} TBV(b:bv32) returns(bool) { true }

function word(i:int) returns(bool);

// meaning undefined if !word(i)
function B(i:int) returns(bv32);
function I(b:bv32) returns(int);

axiom (forall i1:int, i2:int::{B(i1),B(i2)} word(i1) && word(i2) ==> (i1 == i2 <==> B(i1) == B(i2)));
axiom (forall b1:bv32, b2:bv32::{I(b1),I(b2)} b1 == b2 <==> I(b1) == I(b2));

// i1 <= x < i2
function between(i1:int, i2:int, x:int) returns(bool) { i1 <= x && x < i2 }

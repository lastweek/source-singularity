// Dafny prelude
// Created 9 February 2008 by Rustan Leino.
// Copyright (c) 2008, Microsoft.

// ---------------------------------------------------------------
// -- Axiomatization of sets -------------------------------------
// ---------------------------------------------------------------

const Set#Empty: [ref]bool;
axiom (forall o: ref :: { Set#Empty[o] } !Set#Empty[o]);

function Set#Singleton(ref) returns ([ref]bool);
axiom (forall r: ref :: { Set#Singleton(r) } Set#Singleton(r)[r]);
axiom (forall r: ref, o: ref :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);

function Set#UnionOne([ref]bool, ref) returns ([ref]bool);
axiom (forall a: [ref]bool, x: ref, o: ref :: { Set#UnionOne(a,x)[o] }
  Set#UnionOne(a,x)[o] <==> o == x || a[o]);

function Set#Union([ref]bool, [ref]bool) returns ([ref]bool);
axiom (forall a: [ref]bool, b: [ref]bool, o: ref :: { Set#Union(a,b)[o] }
  Set#Union(a,b)[o] <==> a[o] || b[o]);

function Set#Intersection([ref]bool, [ref]bool) returns ([ref]bool);
axiom (forall a: [ref]bool, b: [ref]bool, o: ref :: { Set#Intersection(a,b)[o] }
  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

function Set#Difference([ref]bool, [ref]bool) returns ([ref]bool);
axiom (forall a: [ref]bool, b: [ref]bool, o: ref :: { Set#Difference(a,b)[o] }
  Set#Difference(a,b)[o] <==> a[o] && !b[o]);

function Set#Subset([ref]bool, [ref]bool) returns (bool);
axiom(forall a: [ref]bool, b: [ref]bool :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: ref :: {a[o]} {b[o]} a[o] ==> b[o]));

function Set#Equal([ref]bool, [ref]bool) returns (bool);
axiom(forall a: [ref]bool, b: [ref]bool :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: ref :: {a[o]} {b[o]} a[o] <==> b[o]));

function Set#Disjoint([ref]bool, [ref]bool) returns (bool);
axiom (forall a: [ref]bool, b: [ref]bool :: { Set#Disjoint(a,b) }
  Set#Disjoint(a,b) <==> (forall o: ref :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------
// -- Axiomatization of sequences --------------------------------
// ---------------------------------------------------------------

// Sequence of ref
type Seq;

function Seq#Length(Seq) returns (int);
axiom (forall s: Seq :: { Seq#Length(s) } 0 <= Seq#Length(s));

const Seq#Empty: Seq;
axiom Seq#Length(Seq#Empty) == 0;
axiom (forall s: Seq :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty);

function Seq#Singleton(ref) returns (Seq);
axiom (forall t: ref :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build(s: Seq, index: int, val: ref, newLength: int) returns (Seq);
axiom (forall s: Seq, i: int, v: ref, len: int :: { Seq#Length(Seq#Build(s,i,v,len)) }
  Seq#Length(Seq#Build(s,i,v,len)) == len);

function Seq#Append(Seq, Seq) returns (Seq);
axiom (forall s0: Seq, s1: Seq :: { Seq#Length(Seq#Append(s0,s1)) }
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

function Seq#Index(Seq, int) returns (ref);
axiom (forall t: ref :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
axiom (forall s0: Seq, s1: Seq, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
axiom (forall s: Seq, i: int, v: ref, len: int, n: int :: { Seq#Index(Seq#Build(s,i,v,len),n) }
  (i == n ==> Seq#Index(Seq#Build(s,i,v,len),n) == v) &&
  (i != n ==> Seq#Index(Seq#Build(s,i,v,len),n) == Seq#Index(s,n)));

function Seq#Contains(Seq, ref) returns (bool);
axiom (forall s: Seq, x: ref :: { Seq#Contains(s,x) }
  Seq#Contains(s,x) <==>
    (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));

function Seq#Equal(Seq, Seq) returns (bool);
axiom (forall s0: Seq, s1: Seq :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#SameUntil(Seq, Seq, int) returns (bool);
axiom (forall s0: Seq, s1: Seq, n: int :: { Seq#SameUntil(s0,s1,n) }
  Seq#SameUntil(s0,s1,n) <==>
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#Take(Seq, howMany: int) returns (Seq);
axiom (forall s: Seq, n: int :: { Seq#Length(Seq#Take(s,n)) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
axiom (forall s: Seq, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) }
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop(Seq, howMany: int) returns (Seq);
axiom (forall s: Seq, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
axiom (forall s: Seq, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) }
  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));

// ---------------------------------------------------------------
// -- Boxing and unboxing ----------------------------------------
// ---------------------------------------------------------------

function $BoxBool(bool) returns (ref);
function $UnboxBool(ref) returns (bool);

axiom (forall b: bool :: { $BoxBool(b) } $UnboxBool($BoxBool(b)) == b);

function $BoxInt(int) returns (ref);
function $UnboxInt(ref) returns (int);

axiom (forall x: int :: { $BoxInt(x) } $UnboxInt($BoxInt(x)) == x);

// ---------------------------------------------------------------

type Field;

function $IsGoodHeap([ref,<alpha>Field]alpha) returns (bool);
var $Heap: [ref, <alpha>Field] alpha where $IsGoodHeap($Heap);

const alloc: <bool>Field;

function $HeapSucc([ref,<alpha>Field]alpha, [ref,<alpha>Field]alpha) returns (bool);
axiom (forall h: [ref,<alpha>Field]alpha, k: [ref,<alpha>Field]alpha :: { $HeapSucc(h,k) }
  $HeapSucc(h,k) ==> (forall o: ref :: { k[o,alloc] } h[o,alloc] ==> k[o,alloc]));

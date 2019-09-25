//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// This file contains proofs of the declarations in VerifiedBitVectors.bpl.
// The proofs require assertions to guide the prover.

// Verification requires the "/bv:z" option to enable Z3 support of bit vectors

// Imports:
//   - Trusted.bpl
//   - TrustedBitVectors.bpl
//   - VerifiedBitVectorsBuiltin.bpl
// Exports:
//   - VerifiedBitVectors.bpl

// \Spec#\bin\Boogie.exe /bv:z /noinfer Trusted.bpl TrustedBitVectors.bpl VerifiedBitVectorsBuiltin.bpl VerifiedBitVectors.bpl VerifiedBitVectorsImpl.bpl

function BitIndex(i0:int, i:int) returns(int)
{
  4 * shr(i - i0, 7)
}

function BitZero(x:int, i0:int, i:int) returns(bool)
{
  0 == and(x, shl(1, and(shr(i - i0, 2), 31)))
}

function ColorIndex(i0:int, i:int) returns(int)
{
  4 * shr(i - i0, 6)
}

function ColorGet(x:int, i0:int, i:int) returns(int)
{
  and(shr(x, and(shr(i - i0, 1), 31)), 3)
}

procedure Const()
  ensures 0 == I(0bv32);
  ensures 2 == I(2bv32);
  ensures 3 == I(3bv32);
  ensures 4 == I(4bv32);
  ensures 5 == I(5bv32);
  ensures 6 == I(6bv32);
  ensures 7 == I(7bv32);
  ensures 16 == I(16bv32);
  ensures 32 == I(32bv32);
  ensures 31 == I(31bv32);
  ensures 64 == I(64bv32);
  ensures 63 == I(63bv32);
  ensures 128 == I(128bv32);
  ensures 127 == I(127bv32);
  ensures 256 == I(256bv32);
  ensures 16777215 == I(16777215bv32);
  ensures 33554431 == I(33554431bv32);
  ensures 67108863 == I(67108863bv32);
{
  call $Const();
  assert word(0);
  call _S(1bv32, 1bv32);
  assert word(2);
  call _A(1bv32, 1bv32);
  assert word(3);
  call _A(2bv32, 1bv32);
  assert word(4);
  call _A(2bv32, 2bv32);
  assert word(5);
  call _A(4bv32, 1bv32);
  assert word(6);
  call _A(5bv32, 1bv32);
  assert word(7);
  call _A(5bv32, 2bv32);
  assert word(16);
  call _M(4bv32, 4bv32);
  assert word(32);
  call _A(16bv32, 16bv32);
  assert word(31);
  call _S(32bv32, 1bv32);
  assert word(64);
  call _A(32bv32, 32bv32);
  assert word(63);
  call _S(64bv32, 1bv32);
  assert word(128);
  call _M(32bv32, 4bv32);
  assert word(127);
  call _S(128bv32, 1bv32);
  assert word(I(16bv32) * I(16bv32));
  call _M(16bv32, 16bv32);
  assert word(512);
  call _A(256bv32, 256bv32);
  assert word(65536);
  call _M(256bv32, 256bv32);
  assert word(65535);
  call _S(65536bv32, 1bv32);
  assert word(16777216);
  call _M(65536bv32, 256bv32);
  assert word(16777215);
  call _S(16777216bv32, 1bv32);
  assert word(2147483647 + 2147483647 + 2 - 65536);
  call _M(65536bv32, 65535bv32);
  assert word(33554432);
  call _M(65536bv32, 512bv32);
  assert word(33554431);
  call _S(33554432bv32, 1bv32);
  assert word(67108864);
  call _A(33554432bv32, 33554432bv32);
  assert word(67108863);
  call _S(67108864bv32, 1bv32);
}

procedure Const2()
  ensures 2147483647 + 2147483647 + 1 == I(4294967295bv32);
  ensures 2147483647 + 2147483647 - 2 == I(4294967292bv32);
{
  call Const();
  call $Const();
  assert word(2147483647 + 2147483647 + 1);
  call _A(4294901760bv32, 65535bv32);
  assert word(I(4294967295bv32) - I(3bv32));
  call _S(4294967295bv32, 3bv32);
}

procedure _A(b1:bv32, b2:bv32)
  requires word(I(b1) + I(b2));
  ensures  I(b1) + I(b2) == I($add(b1, b2));
{
  assert TBV(b1) && TBV(b2);
}

procedure _S(b1:bv32, b2:bv32)
  requires word(I(b1) - I(b2));
  ensures  I(b1) - I(b2) == I($sub(b1, b2));
{
  assert TBV(b1) && TBV(b2);
}

procedure _M(b1:bv32, b2:bv32)
  requires word(I(b1) * I(b2));
  ensures  I(b1) * I(b2) == I($mul(b1, b2));
{
  assert TBV(b1) && TBV(b2);
}

implementation __andAligned(x:int)
{
  call Const();
  call $AndAligned(B(x));
  assert Aligned(I(B(x))) <==> $Aligned(B(x));
}

implementation __addAligned(x:int, y:int)
{
  call Const();
  call $AddAligned(B(x), B(y));
  assert word(x) && word(y) && word(x + y) && Aligned(I(B(x))) ==> (Aligned(I(B(y))) <==> Aligned(I(B(x + y))));
}

implementation __subAligned(x:int, y:int)
{
  call Const();
  call $SubAligned(B(x), B(y));
  assert word(x) && word(y) && word(x - y) && Aligned(I(B(x))) ==> (Aligned(I(B(y))) <==> Aligned(I(B(x - y))));
}

implementation __notAligned(i:int)
{
  call Const();
  call Const2();
  call $NotAligned(B(i));
  assert TBV(B(i)) && TBV(4294967292bv32);
  assert i <= 2147483647 + 2147483647 - 2;
}

implementation __initialize($unitSize:int, HeapLo:int)
{
  call Const();
  assert $le(B($unitSize), B(16777215));
  call $Initialize(B($unitSize));
  assert BitIndex(HeapLo, HeapLo + 128 * $unitSize) == 4 * $unitSize;
  assert BitIndex(HeapLo, HeapLo + 256 * $unitSize) == 8 * $unitSize;
}

implementation __bb4Zero(a:[int]int, off:int, aBase:int, bb:[int]int, i0:int, i1:int, i2:int, g1:int, g2:int, idx:int)
{
  call Const();

  assert word(idx) && word(g1);
  assert word(I(B(idx)) - I(B(g1)));
  assert $le($shr(B(i2 - i0), 7bv32), 33554431bv32) ==> I($mul(128bv32, $shr(B(i2 - i0), 7bv32))) == 128 * I($shr(B(i2 - i0), 7bv32));
  assert  (forall i:int::{TV(i)} TV(i) && word(i - i0) && i1 <= i && i < i2 && Aligned(I(B(i - i0))) ==> $Aligned(B(i - i0)));

  call _BB4Zero(a, off, aBase, bb, i0, i1, i2, g1, g2, idx);
}

implementation __bb4GetBit(a:[int]int, off:int, aBase:int, bb:[int]int, i0:int, i1:int, i2:int, k:int, idx:int, bbb:int, g1:int, g2:int)
{
  call Const();
  call _BB4GetBit(i0, k);
}

implementation __bb4SetBit(a:[int]int, on:int, off:int, aBase:int, bb:[int]int, i0:int, i1:int, i2:int, k:int, idx:int, bbb:int, ret:[int]int, g1:int, g2:int)
{
  call Const();

  assert B(shr(k - i0, 7)) == $shr(B(k - i0), 7bv32);
  assert Aligned(I(B(k - i0)));
  assert  (forall i:int::{TV(i)} TV(i) && word(i - i0) && i1 <= i && i < i2 && Aligned(I(B(i - i0))) ==> $Aligned(B(i - i0)));

  call _BB4SetBit(a, on, off, aBase, bb, i0, i1, i2, k, idx, bbb, ret, g1, g2);

  assert $bbvec4(a[aBase + (k - i0) := on], off, aBase, ret, i0, i1, i2, g1, g2);
}

implementation __bb4Zero2(a:[int]int, aBase:int, bb:[int]int, i0:int, i1:int, i2:int, g1:int, g2:int, idx:int)
{
  call Const();

  assert word(idx) && word(g1);
  assert word(I(B(idx)) - I(B(g1)));
  assert $le($shr(B(i2 - i0), 6bv32), 67108863bv32) ==> I($mul(64bv32, $shr(B(i2 - i0), 6bv32))) == 64 * I($shr(B(i2 - i0), 6bv32));
  assert  (forall i:int::{TV(i)} TV(i) && word(i - i0) && i1 <= i && i < i2 && Aligned(I(B(i - i0))) ==> $Aligned(B(i - i0)));

  call _BB4Zero2(a, aBase, bb, i0, i1, i2, g1, g2, idx);
}

implementation __bb4Get2Bit(a:[int]int, aBase:int, bb:[int]int, i0:int, i1:int, i2:int, k:int, idx:int, bbb:int, g1:int, g2:int)
{
  call Const();
  call _BB4Get2Bit(i0, k);
}

implementation __bb4Set2Bit(a:[int]int, val:int, aBase:int, bb:[int]int, i0:int, i1:int, i2:int, k:int, idx:int, bbb:int, _bbb:int, ret:[int]int, g1:int, g2:int)
{
  call Const();

  assert  (forall i:int::{TV(i)} TV(i) && word(i - i0) && i1 <= i && i < i2 && Aligned(I(B(i - i0))) ==> $Aligned(B(i - i0)));

  call _BB4Set2Bit(a, val, aBase, bb, i0, i1, i2, k, idx, bbb, _bbb, ret, g1, g2);
}





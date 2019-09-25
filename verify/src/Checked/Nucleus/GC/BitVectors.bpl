//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// This file contains proofs of the declarations in VerifiedBitVectors.bpl.
// The proofs require assertions to guide the prover.

// Verification requires the "/bv:z" option to enable Z3 support of bit vectors

axiom (forall i0:int,i:int::BitIndex(i0, i) == 4 * shr(i - i0, 7));

axiom (forall x:int,i0:int,i:int::BitZero(x, i0, i) ==
  (0 == and(x, shl(1, and(shr(i - i0, 2), 31)))));

axiom (forall i0:int,i:int::ColorIndex(i0, i) == 4 * shr(i - i0, 6));

axiom (forall x:int,i0:int,i:int::ColorGet(x, i0, i) ==
  (and(shr(x, and(shr(i - i0, 1), 31)), 3)));

procedure _a($b1:bv32, $b2:bv32)
  requires word(I($b1) + I($b2));
  ensures  I($b1) + I($b2) == I($add($b1, $b2));
{
  assert TBV($b1) && TBV($b2);
}

procedure _s($b1:bv32, $b2:bv32)
  requires word(I($b1) - I($b2));
  ensures  I($b1) - I($b2) == I($sub($b1, $b2));
{
  assert TBV($b1) && TBV($b2);
}

procedure _m($b1:bv32, $b2:bv32)
  requires word(I($b1) * I($b2));
  ensures  I($b1) * I($b2) == I($mul($b1, $b2));
{
  assert TBV($b1) && TBV($b2);
}

procedure __const()
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
  call _const();
  assert word(0);
  call _s(1bv32, 1bv32);
  assert word(2);
  call _a(1bv32, 1bv32);
  assert word(3);
  call _a(2bv32, 1bv32);
  assert word(4);
  call _a(2bv32, 2bv32);
  assert word(5);
  call _a(4bv32, 1bv32);
  assert word(6);
  call _a(5bv32, 1bv32);
  assert word(7);
  call _a(5bv32, 2bv32);
  assert word(16);
  call _m(4bv32, 4bv32);
  assert word(32);
  call _a(16bv32, 16bv32);
  assert word(31);
  call _s(32bv32, 1bv32);
  assert word(64);
  call _a(32bv32, 32bv32);
  assert word(63);
  call _s(64bv32, 1bv32);
  assert word(128);
  call _m(32bv32, 4bv32);
  assert word(127);
  call _s(128bv32, 1bv32);
  assert word(I(16bv32) * I(16bv32));
  call _m(16bv32, 16bv32);
  assert word(512);
  call _a(256bv32, 256bv32);
  assert word(65536);
  call _m(256bv32, 256bv32);
  assert word(65535);
  call _s(65536bv32, 1bv32);
  assert word(16777216);
  call _m(65536bv32, 256bv32);
  assert word(16777215);
  call _s(16777216bv32, 1bv32);
  assert word(2147483647 + 2147483647 + 2 - 65536);
  call _m(65536bv32, 65535bv32);
  assert word(33554432);
  call _m(65536bv32, 512bv32);
  assert word(33554431);
  call _s(33554432bv32, 1bv32);
  assert word(67108864);
  call _a(33554432bv32, 33554432bv32);
  assert word(67108863);
  call _s(67108864bv32, 1bv32);
}

procedure __const2()
  ensures 2147483647 + 2147483647 + 1 == I(4294967295bv32);
  ensures 2147483647 + 2147483647 - 2 == I(4294967292bv32);
{
  call __const();
  call _const();
  assert word(2147483647 + 2147483647 + 1);
  call _a(4294901760bv32, 65535bv32);
  assert word(I(4294967295bv32) - I(3bv32));
  call _s(4294967295bv32, 3bv32);
}

procedure __const3()
  ensures 4096 == I(4096bv32);
  ensures 4095 == I(4095bv32);
{
  call __const();
  call _const();
  assert word(4096);
  assert word(I(64bv32) * I(64bv32));
  call _m(64bv32, 64bv32);
  assert word(4095);
  call _s(4096bv32, 1bv32);
}

procedure __const4()
  ensures 2097152 == I(2097152bv32);
  ensures 2097151 == I(2097151bv32);
{
  call __const();
  call _const();
  assert word(2097152);
  assert word(I(32bv32) * I(65536bv32));
  call _m(32bv32, 65536bv32);
  assert word(2097151);
  call _s(2097152bv32, 1bv32);
}

implementation __zeroAligned()
{
  call __const();
  call _zeroAligned();
}

implementation __andAligned($x:int)
{
  call __const();
  call _andAligned(B($x));
  assert Aligned(I(B($x))) <==> $Aligned(B($x));
}

implementation __addAligned($x:int, $y:int)
{
  call __const();
  call _addAligned(B($x), B($y));
  assert word($x) && word($y) && word($x + $y) && Aligned(I(B($x))) ==> (Aligned(I(B($y))) <==> Aligned(I(B($x + $y))));
}

implementation __subAligned($x:int, $y:int)
{
  call __const();
  call _subAligned(B($x), B($y));
  assert word($x) && word($y) && word($x - $y) && Aligned(I(B($x))) ==> (Aligned(I(B($y))) <==> Aligned(I(B($x - $y))));
}

implementation __notAligned($i:int)
{
  call __const();
  call __const2();
  call _notAligned(B($i));
  assert TBV(B($i)) && TBV(4294967292bv32);
  assert $i <= 2147483647 + 2147483647 - 2;
}

implementation __is4kAligned($x:int)
{
  call __const();
  call __const3();
  call _is4kAligned(B($x));
}

implementation __is2m4kAligned($x:int)
{
  call __const();
  call __const3();
  call __const4();
  call _is2m4kAligned(B($x));
}

implementation __add4kAligned($x:int)
{
  call __const();
  call __const3();
  call _add4kAligned(B($x));
}

implementation __initialize($unitSize:int, $heapLo:int)
{
  call __const();
  assert $le(B($unitSize), B(16777215));
  call _initialize(B($unitSize));
  assert BitIndex($heapLo, $heapLo + 128 * $unitSize) == 4 * $unitSize;
  assert BitIndex($heapLo, $heapLo + 256 * $unitSize) == 8 * $unitSize;
}

implementation __bb4Zero($a:[int]int, $off:int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $g1:int, $g2:int, $idx:int)
{
  call __const();

  assert word($idx) && word($g1);
  assert word(I(B($idx)) - I(B($g1)));
  assert $le($shr(B($i2 - $i0), 7bv32), 33554431bv32) ==> I($mul(128bv32, $shr(B($i2 - $i0), 7bv32))) == 128 * I($shr(B($i2 - $i0), 7bv32));
  assert  (forall $i:int::{TV($i)} TV($i) && word($i - $i0) && $i1 <= $i && $i < $i2 && Aligned(I(B($i - $i0))) ==> $Aligned(B($i - $i0)));

  call _bb4Zero($a, $off, $aBase, $bb, $i0, $i1, $i2, $g1, $g2, $idx);
}

implementation __bb4GetBit($a:[int]int, $off:int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $k:int, $idx:int, $bbb:int, $g1:int, $g2:int)
{
  call __const();
  call _bb4GetBit($i0, $k);
}

implementation __bb4SetBit($a:[int]int, $on:int, $off:int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $k:int, $idx:int, $bbb:int, $ret:[int]int, $g1:int, $g2:int)
{
  call __const();

  assert B(shr($k - $i0, 7)) == $shr(B($k - $i0), 7bv32);
  assert Aligned(I(B($k - $i0)));
  assert  (forall $i:int::{TV($i)} TV($i) && word($i - $i0) && $i1 <= $i && $i < $i2 && Aligned(I(B($i - $i0))) ==> $Aligned(B($i - $i0)));

  call _bb4SetBit($a, $on, $off, $aBase, $bb, $i0, $i1, $i2, $k, $idx, $bbb, $ret, $g1, $g2);

  assert $bbvec4($a[$aBase + ($k - $i0) := $on], $off, $aBase, $ret, $i0, $i1, $i2, $g1, $g2);
}

implementation __bb4Zero2($a:[int]int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $g1:int, $g2:int, $idx:int)
{
  call __const();

  assert word($idx) && word($g1);
  assert word(I(B($idx)) - I(B($g1)));
  assert $le($shr(B($i2 - $i0), 6bv32), 67108863bv32) ==> I($mul(64bv32, $shr(B($i2 - $i0), 6bv32))) == 64 * I($shr(B($i2 - $i0), 6bv32));
  assert  (forall $i:int::{TV($i)} TV($i) && word($i - $i0) && $i1 <= $i && $i < $i2 && Aligned(I(B($i - $i0))) ==> $Aligned(B($i - $i0)));

  call _bb4Zero2($a, $aBase, $bb, $i0, $i1, $i2, $g1, $g2, $idx);
}

implementation __bb4Get2Bit($a:[int]int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $k:int, $idx:int, $bbb:int, $g1:int, $g2:int)
{
  call __const();
  call _bb4Get2Bit($i0, $k);
}

implementation __bb4Set2Bit($a:[int]int, $val:int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $k:int, $idx:int, $bbb:int, $_bbb:int, $ret:[int]int, $g1:int, $g2:int)
{
  call __const();

  assert  (forall $i:int::{TV($i)} TV($i) && word($i - $i0) && $i1 <= $i && $i < $i2 && Aligned(I(B($i - $i0))) ==> $Aligned(B($i - $i0)));

  call _bb4Set2Bit($a, $val, $aBase, $bb, $i0, $i1, $i2, $k, $idx, $bbb, $_bbb, $ret, $g1, $g2);
}





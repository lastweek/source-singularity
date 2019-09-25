//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

function BitIndex(i0:int, i:int) returns(int);
function BitZero(x:int, i0:int, i:int) returns(bool);
function ColorIndex(i0:int, i:int) returns(int);
function ColorGet(x:int, i0:int, i:int) returns(int);

function bbvec4(a:[int]int, off:int, aBase:int, bb:[int]int, i0:int, i1:int, i2:int, g1:int, g2:int) returns(bool)
{
  (forall i:int::{TV(i)} TV(i) && i1 <= i && i < i2 && Aligned(i - i0) ==>
       between(g1, g2, g1 + BitIndex(i0, i))
    && (a[aBase + (i - i0)] == off <==> BitZero(bb[g1 + BitIndex(i0, i)], i0, i))
  )
}

function bb2vec4(a:[int]int, aBase:int, bb:[int]int, i0:int, i1:int, i2:int, g1:int, g2:int) returns(bool)
{
  (forall i:int::{TV(i)} TV(i) && word(i - i0) && i1 <= i && i < i2 && Aligned(i - i0) ==>
       between(g1, g2, g1 + ColorIndex(i0, i))
    && (a[aBase + (i - i0)] == ColorGet(bb[g1 + ColorIndex(i0, i)], i0, i))
  )
}

procedure __zeroAligned();
  ensures  Aligned(0);

procedure __andAligned($x:int);
  ensures  word($x) ==> (and($x, 3) == 0 <==> Aligned($x));

procedure __addAligned($x:int, $y:int);
  ensures  word($x) && word($y) && word($x + $y) && Aligned($x) ==>
             (Aligned($y) <==> Aligned($x + $y));

procedure __subAligned($x:int, $y:int);
  ensures  word($x) && word($y) && word($x - $y) && Aligned($x) ==>
             (Aligned($y) <==> Aligned($x - $y));

procedure __notAligned($i:int);
  requires Aligned($i);
  requires word($i);
  ensures  !Aligned($i + 1);
  ensures  !Aligned($i + 2);
  ensures  !Aligned($i + 3);
  ensures  word($i + 1);
  ensures  word($i + 2);
  ensures  word($i + 3);

procedure __is4kAligned($x:int);
  requires word($x) && word($x - 4096);
  ensures  and($x - and($x, 4095), 4095) == 0;
  ensures  0 <= and($x, 4095) && and($x, 4095) <= 4095;

procedure __add4kAligned($x:int);
  requires and($x, 4095) == 0;
  requires word($x) && word($x + 4096);
  ensures  and($x + 4096, 4095) == 0;
  ensures  Aligned($x);

procedure __is2m4kAligned($x:int);
  requires word($x) && word($x - 2097152) && word($x + 2097152);
  ensures  and($x + 2097152 - and($x, 2097151), 4095) == 0;
  ensures  0 <= and($x, 2097151) && and($x, 2097151) <= 2097151;

procedure __initialize($unitSize:int, $heapLo:int);
  requires word($unitSize * 256);
  ensures BitIndex($heapLo, $heapLo) == 0;
  ensures BitIndex($heapLo, $heapLo + 128 * $unitSize) == 4 * $unitSize;
  ensures BitIndex($heapLo, $heapLo + 256 * $unitSize) == 8 * $unitSize;

procedure __bb4Zero($a:[int]int, $off:int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $g1:int, $g2:int, $idx:int);
  requires (forall $i:int::{TV($i)} TV($i) && $i1 <= $i && $i < $i2 + 128 ==> $a[$aBase + ($i - $i0)] == $off);
  requires bbvec4($a, $off, $aBase, $bb, $i0, $i1, $i2, $g1, $g2);
  requires word($i1 - $i0) && word($i2 - $i0) && word($i2 - $i1) && word($i2 + 128 - $i0);
  requires word($idx) && word($g1);
  requires Aligned($idx) && Aligned($g1);
  requires $i2 - $i1 == 32 * ($idx - $g1);
  requires $i1 == $i0;
  requires between($g1, $g2, $idx);
  ensures  bbvec4($a, $off, $aBase, $bb[$idx := 0], $i0, $i1, $i2 + 128, $g1, $g2);

procedure __bb4GetBit($a:[int]int, $off:int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $k:int, $idx:int, $bbb:int, $g1:int, $g2:int);
  requires bbvec4($a, $off, $aBase, $bb, $i0, $i1, $i2, $g1, $g2);
  requires TV($k) && word($k - $i0) && $i1 <= $k && $k < $i2 && Aligned($k - $i0);
  requires $idx == $g1 + 4 * shr($k - $i0, 7);
  requires $bbb == and($bb[$idx], shl(1, and(shr($k - $i0, 2), 31)));
  requires word($i1 - $i0) && word($i2 - $i0);
  ensures  between($g1, $g2, $idx);
  ensures  and(shr($k - $i0, 2), 31) < 32;
  ensures  $bbb == 0 <==> $a[$aBase + ($k - $i0)] == $off;

procedure __bb4SetBit($a:[int]int, $on:int, $off:int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $k:int, $idx:int, $bbb:int, $ret:[int]int, $g1:int, $g2:int);
  requires bbvec4($a, $off, $aBase, $bb, $i0, $i1, $i2, $g1, $g2);
  requires TV($k) && word($k - $i0) && $i1 <= $k && $k < $i2 && Aligned($k - $i0);
  requires $on != $off;
  requires $idx == $g1 + 4 * shr($k - $i0, 7);
  requires $bbb == or($bb[$idx], shl(1, and(shr($k - $i0, 2), 31)));
  requires $ret == $bb[$idx := $bbb];
  requires word($i1 - $i0) && word($i2 - $i0);
  ensures  bbvec4($a[$aBase + ($k - $i0) := $on], $off, $aBase, $ret, $i0, $i1, $i2, $g1, $g2);
  ensures  between($g1, $g2, $idx);
  ensures  and(shr($k - $i0, 2), 31) < 32;
  ensures  4 * shr($k - $i0, 7) == BitIndex($i0, $k);

procedure __bb4Zero2($a:[int]int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $g1:int, $g2:int, $idx:int);
  requires (forall $i:int::{TV($i)} TV($i) && $i1 <= $i && $i < $i2 + 64 ==> $a[$aBase + ($i - $i0)] == 0);
  requires bb2vec4($a, $aBase, $bb, $i0, $i1, $i2, $g1, $g2);
  requires word($i1 - $i0) && word($i2 - $i0) && word($i2 - $i1) && word($i2 + 64 - $i0);
  requires word($idx) && word($g1);
  requires Aligned($idx) && Aligned($g1);
  requires $i2 - $i1 == 16 * ($idx - $g1);
  requires $i1 == $i0;
  requires between($g1, $g2, $idx);
  ensures  bb2vec4($a, $aBase, $bb[$idx := 0], $i0, $i1, $i2 + 64, $g1, $g2);

procedure __bb4Get2Bit($a:[int]int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $k:int, $idx:int, $bbb:int, $g1:int, $g2:int);
  requires bb2vec4($a, $aBase, $bb, $i0, $i1, $i2, $g1, $g2);
  requires TV($k) && word($k - $i0) && $i1 <= $k && $k < $i2 && Aligned($k - $i0);
  requires $idx == $g1 + 4 * shr($k - $i0, 6);
  requires $bbb == and(shr($bb[$idx], and(shr($k - $i0, 1), 31)), 3);
  ensures  $a[$aBase + ($k - $i0)] == $bbb;
  ensures  between($g1, $g2, $idx);
  ensures  and(shr($k - $i0, 1), 31) <= 31;

procedure __bb4Set2Bit($a:[int]int, $val:int, $aBase:int, $bb:[int]int, $i0:int, $i1:int, $i2:int, $k:int, $idx:int, $bbb:int, $_bbb:int, $ret:[int]int, $g1:int, $g2:int);
  requires bb2vec4($a, $aBase, $bb, $i0, $i1, $i2, $g1, $g2);
  requires TV($k) && word($k - $i0) && $i1 <= $k && $k < $i2 && Aligned($k - $i0);
  requires $idx == $g1 + 4 * shr($k - $i0, 6);
  requires 0 <= $val && $val <= 3;
  requires $bbb == and($bb[$idx], neg(shl(3, and(shr($k - $i0, 1), 31))));
  requires $_bbb == or($bbb, shl($val, and(shr($k - $i0, 1), 31)));
  requires $ret == $bb[$idx := $_bbb];
  ensures  bb2vec4($a[$aBase + ($k - $i0) := $val], $aBase, $ret, $i0, $i1, $i2, $g1, $g2);
  ensures  between($g1, $g2, $idx);
  ensures  and(shr($k - $i0, 1), 31) <= 31;
  ensures  4 * shr($k - $i0, 6) == ColorIndex($i0, $k);


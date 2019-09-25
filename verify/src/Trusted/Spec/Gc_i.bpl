//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// Each managed stack $s grows from StackHi($s) down to StackLo($s)
function StackHi($s:int) returns(int);
function StackLo($s:int) returns(int);

// Requirement on entry to Nucleus from managed call:
// Since interrupts are disabled when calling the Nucleus, we do not
// require ?InterruptReserve be reserved between StackLo and esp.
function SpRequire($s:int, sp:int, n:int) returns(bool)
{
    StackLo($s) <= sp && sp + n <= StackHi($s) && Aligned(sp)
}

function StackCheckInv($s:int, StackCheck:int) returns(bool)
{
    StackLo($s) + ?StackReserve + ?InterruptReserve <= StackCheck
 && StackCheck <= StackHi($s)
}

function ScanStackInv($S:int, $Mem:[int]int,
  $FrameCounts:[int]int, $FrameAddrs:[int][int]int, $FrameLayouts:[int][int]$FrameLayout,
  $FrameSlices:[int][int]int, $FrameAbss:[int][int][int]int, $FrameOffsets:[int][int]int,
  $ra:int, $esp:int, $ebp:int) returns(bool)
{
    0 <= $FrameCounts[$S]
 && $FrameSlices[$S][$esp] == $FrameCounts[$S] && $Mem[$esp] == $ra
 && FrameNextInv($FrameCounts[$S], $ra, $ebp, $FrameAddrs[$S], $FrameLayouts[$S])
 && StackInvS($S, $FrameVars)
}

// Call the garbage collector.
// REVIEW: most system calls will share these preconditions and postconditions, so we should define some more abbreviations
procedure GarbageCollect();
  // GC invariant:
  requires word(ebp);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires SpRequire($S, esp, 4);
  requires ReturnToAddr($Mem[esp]) == $RET;

  // requirements on mutator root layout:
  requires ScanStackInv($S, $Mem, $FrameVars, $Mem[esp], esp, ebp);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs);

  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $toAbs, AllGcVars, $MemVars, $SectionMem;

  ensures  SMemEnsure($sMem, old($sMem), esp, old(esp));
  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs);
  ensures  StackInvS($S, $FrameVars);
  ensures  NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
  ensures  esp == old(esp) + 4;

// Prepare to call Load (don't actually call it -- let the mutator call it)
// This procedure executes no instructions (it is not allowed to modify $Eip)
procedure readField($ptr:int, $fld:int) returns ($val:int);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires Pointer($toAbs, $ptr, $toAbs[$ptr]);
  requires 0 <= $fld && $fld < numFields($toAbs[$ptr]);
  ensures  gcAddr($ptr + 4 * $fld);
  ensures  $val == $Mem[$ptr + 4 * $fld];
  ensures  Value(VFieldPtr($toAbs[$ptr], $fld), $toAbs, $val, $AbsMem[$toAbs[$ptr]][$fld]);

// Prepare to call Store (don't actually call it -- let the mutator call it)
// This procedure executes no instructions (it is not allowed to modify $Eip)
procedure writeField($ptr:int, $fld:int, $val:int, $abs:int) returns ($_mem:[int]int, $_absMem:[int][int]int);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $Mem, $memVars, MemVars, $FrameVars, $IoVars);
  requires Pointer($toAbs, $ptr, $toAbs[$ptr]);
  requires 0 <= $fld && $fld < numFields($toAbs[$ptr]);
  requires !isReadonlyField(tag($AbsMem[$toAbs[$ptr]][1]), $fld);
  requires Value(VFieldPtr($toAbs[$ptr], $fld), $toAbs, $val, $abs);
  modifies AllGcVars, $memVars; // ... but don't modify $Mem
  ensures  gcAddr($ptr + 4 * $fld);
  ensures  word($val);
  ensures  $_mem == $Mem[$ptr + 4 * $fld := $val];
  ensures  $_absMem == $AbsMem[$toAbs[$ptr] := $AbsMem[$toAbs[$ptr]][$fld := $abs]];
  ensures  NucleusInv($S, $StackState, $toAbs, $_absMem, GcVars, $_mem, $memVars, MemVars, $FrameVars, $IoVars);

// Prepare to call Load (don't actually call it -- let the mutator call it)
// This procedure executes no instructions (it is not allowed to modify $Eip)
procedure readStack($ptr:int, $frame:int, $j:int) returns ($val:int);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires 0 <= $frame && $frame < $FrameCounts[$S];
  requires $FrameSlices[$S][$ptr] == $frame;
  requires $ptr == $FrameAddrs[$S][$frame] + 4 * $j; // REVIEW: redundant?
  ensures  memAddr($ptr);
  ensures  !gcAddrEx($ptr);
  ensures  $val == $Mem[$ptr];
  ensures  InteriorValue(frameHasPtr($FrameLayouts[$S][$frame], $j), $toAbs, $val, $FrameAbss[$S][$frame][$j], $FrameOffsets[$S][$ptr]);

// Prepare to call Store (don't actually call it -- let the mutator call it)
// This procedure executes no instructions (it is not allowed to modify $Eip)
procedure writeStack(
    $ptr:int, $val:int, $frame:int, $j:int, $fX:[int]int, $jX:[int]int,
    $_frameCount:int, $_frameAddr:[int]int, $_frameLayout:[int]$FrameLayout,
    $_frameSlice:[int]int, $_frameAbs:[int][int]int, $_frameOffset:[int]int)
    returns ($_mem:[int]int);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $Mem, $memVars, MemVars,
            $FrameCounts, $FrameAddrs, $FrameLayouts, $FrameSlices, $FrameAbss, $FrameOffsets, $IoVars);
  requires $_frameSlice[$ptr] == $frame;
  requires $ptr == $_frameAddr[$frame] + 4 * $j;
  requires StackLo($S) <= $ptr && $ptr < StackHi($S);
  requires Aligned($ptr);
  requires InteriorValue(frameHasPtr($_frameLayout[$frame], $j), $toAbs, $val, $_frameAbs[$frame][$j], $_frameOffset[$ptr]);
  // REVIEW: this requirement is messy:
  // All stack slots in the new stack, except for $ptr, map to an identical slot in the old stack:
  requires (forall f:int,j:int::{TV(f),TO(j)} TV(f) && TO(j) ==>
             0 <= f && f < $_frameCount && $_frameSlice[$_frameAddr[f] + 4 * j] == f ==>
             $_frameAddr[f] + 4 * j != $ptr ==>
                  0 <= $fX[f] && $fX[f] < $FrameCounts[$S]
               && $FrameSlices[$S][$FrameAddrs[$S][$fX[f]] + 4 * $jX[j]] == $fX[f]
               && $_frameAddr[f] + 4 * j == $FrameAddrs[$S][$fX[f]] + 4 * $jX[j]
               && $_frameAbs[f][j] == $FrameAbss[$S][$fX[f]][$jX[j]]
               && frameHasPtr($_frameLayout[f], j) == frameHasPtr($FrameLayouts[$S][$fX[f]], $jX[j])
               && $_frameOffset[$_frameAddr[f] + 4 * j] == $FrameOffsets[$S][$FrameAddrs[$S][$fX[f]] + 4 * $jX[j]]);
  modifies $fMems; /// ... but don't modify $Mem
  ensures  $_mem == $Mem[$ptr := $val];
  ensures  memAddr($ptr);
  ensures  !gcAddrEx($ptr);
  ensures  word($val);
  ensures  NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $_mem, $memVars, MemVars,
            $FrameCounts [$S := $_frameCount],
            $FrameAddrs  [$S := $_frameAddr],
            $FrameLayouts[$S := $_frameLayout],
            $FrameSlices [$S := $_frameSlice],
            $FrameAbss   [$S := $_frameAbs],
            $FrameOffsets[$S := $_frameOffset],
            $IoVars);

procedure AllocObject($abs:int, $vt:int);
  // GC invariant:
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires SpRequire($S, esp, 4);
  requires ReturnToAddr($Mem[esp]) == $RET;

  // requirements on mutator root layout:
  requires ScanStackInv($S, $Mem, $FrameVars, $Mem[esp], esp, ebp);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs);

  // requirements on vtable and layout:
  requires ecx == $vt;
  requires word($vt) && !gcAddrEx($vt);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, 0, 0);
  requires !isVarSize(tag($vt));

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires (forall j:int::{TO(j)} TO(j) ==> 2 <= j && j < numFields($abs) ==> $AbsMem[$abs][j] == NULL);

  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $toAbs, AllGcVars, $MemVars, $SectionMem;

  ensures  SMemEnsure($sMem, old($sMem), esp, old(esp));
  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs);
  ensures  StackInvS($S, $FrameVars);
  ensures  NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  ensures  eax == 0 || Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
  ensures  esp == old(esp) + 4;

procedure AllocString($abs:int, $vt:int, $nElems:int);
  // GC invariant:
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires SpRequire($S, esp, 4);
  requires ReturnToAddr($Mem[esp]) == $RET;

  // requirements on mutator root layout:
  requires ScanStackInv($S, $Mem, $FrameVars, $Mem[esp], esp, ebp);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs);

  // requirements on vtable and layout:
  requires ecx == $nElems - 1;
  requires $vt == ?STRING_VTABLE;
  requires word($vt) && !gcAddrEx($vt);
  requires word($nElems);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $nElems, 0);
  requires tag($vt) == ?STRING_TAG;

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires $AbsMem[$abs][2] == $nElems;
  requires $AbsMem[$abs][3] == $nElems - 1;
  requires (forall j:int::{TO(j)} TO(j) ==> 4 <= j && 4 * j < pad(16 + 2 * $nElems) ==> $AbsMem[$abs][j] == NULL);

  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $toAbs, AllGcVars, $MemVars, $SectionMem;

  ensures  SMemEnsure($sMem, old($sMem), esp, old(esp));
  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs);
  ensures  StackInvS($S, $FrameVars);
  ensures  NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  ensures  eax == 0 || Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
  ensures  esp == old(esp) + 4;

procedure AllocArray($abs:int, $vt:int, $rank:int, $nElems:int);
  // GC invariant:
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires SpRequire($S, esp, 8);
  requires ReturnToAddr($Mem[esp]) == $RET;
  requires $FrameSlices[$S][esp + 4] == $FrameCounts[$S];

  // requirements on mutator root layout:
  requires ScanStackInv($S, $Mem, $FrameVars, $Mem[esp], esp, ebp);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs);

  // requirements on vtable and layout:
  requires ecx == $vt;
  requires edx == $rank;
  requires $FrameSlices[$S][esp + 4] == $FrameCounts[$S] && $fMems[$S][esp + 4] == $nElems;
  requires word($vt) && !gcAddrEx($vt);
  requires word($rank);
  requires word($nElems);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $rank, $nElems);
  requires tag($vt) == ?PTR_ARRAY_TAG || tag($vt) == ?OTHER_ARRAY_TAG;

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires $AbsMem[$abs][2] == $rank;
  requires $AbsMem[$abs][3] == $nElems;
  requires (forall j:int::{TO(j)} TO(j) ==> 4 <= j && j < numFields($abs) ==> $AbsMem[$abs][j] == NULL);

  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $toAbs, AllGcVars, $MemVars, $SectionMem;

  ensures  SMemEnsure($sMem, old($sMem), esp, old(esp));
  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs);
  ensures  StackInvS($S, $FrameVars);
  ensures  NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  ensures  eax == 0 || Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
  ensures  esp == old(esp) + 4;

procedure AllocVector($abs:int, $vt:int, $nElems:int);
  // GC invariant:
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires SpRequire($S, esp, 4);
  requires ReturnToAddr($Mem[esp]) == $RET;

  // requirements on mutator root layout:
  requires ScanStackInv($S, $Mem, $FrameVars, $Mem[esp], esp, ebp);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs);

  // requirements on vtable and layout:
  requires ecx == $vt;
  requires edx == $nElems;
  requires word($vt) && !gcAddrEx($vt);
  requires word($nElems);
  requires VTable($abs, $vt);
  requires ObjSize($abs, $vt, $nElems, 0);
  requires tag($vt) == ?PTR_VECTOR_TAG || tag($vt) == ?OTHER_VECTOR_TAG;

  // require a fresh, empty abstract node:
  requires $abs != NO_ABS;
  requires (forall i:int::{TV(i)} TV(i) ==> gcAddr(i) ==> $toAbs[i] != $abs);
  requires $AbsMem[$abs][0] == NULL;
  requires $AbsMem[$abs][1] == $vt;
  requires $AbsMem[$abs][2] == $nElems;
  requires (forall j:int::{TO(j)} TO(j) ==> 3 <= j && j < numFields($abs) ==> $AbsMem[$abs][j] == NULL);

  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $toAbs, AllGcVars, $MemVars, $SectionMem;

  ensures  SMemEnsure($sMem, old($sMem), esp, old(esp));
  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs);
  ensures  StackInvS($S, $FrameVars);
  ensures  NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  ensures  eax == 0 || Pointer($toAbs, eax - 4, $abs);
  ensures  WellFormed($toAbs);
  ensures  ebp == old(ebp);
  ensures  esp == old(esp) + 4;


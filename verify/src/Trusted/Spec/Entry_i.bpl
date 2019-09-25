//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

//////////////////////////////////////////////////////////////////////////////
//
// This procedure is the entry point from the boot loader.
//
//////////////////////////////////////////////////////////////////////////////
// ecx points to the platform structure
//   ecx + 4 * 11 contains the smap count
//   ecx + 4 * 10 points to the smap
//     smap + 24 * 3 points to smap entry 3
//     smap + 24 * 3 + 0 contains the entry base address
//     smap + 24 * 3 + 8 contains the entry size
//     smap + 24 * 3 + 16 contains the entry type (type == 1 ==> available)
procedure NucleusEntryPoint($smap:int);
  requires inRo(ecx + 40, 4);
  requires inRo(ecx + 44, 4);
  requires ro32(ecx + 44) >= 4 ==>
              $smap == ro32(ecx + 40)
           && inRo($smap + 3 * 24, 4) && inRo($smap + 3 * 24 + 8, 4) && inRo($smap + 3 * 24 + 16, 4)
           && (ro32($smap + 3 * 24 + 16) == 1 ==>
                  ?idtLo == ro32($smap + 3 * 24 + 0)
               && ?memHi == ro32($smap + 3 * 24 + 8) + ?idtLo);
  requires ?idtHi == ?iomLo;
  requires ?iomHi == ?dmaLo;
  requires ?dmaHi == ?memLo;
  requires Aligned(esp);
  requires $S == ?InitialStack;
  requires (forall $s:int::{$StackState[$s]} 0 <= $s && $s < ?NumStacks ==> StackStateTag($StackState[$s]) == ?STACK_EMPTY);
  requires $RET == ReturnToAddr(?KernelEntryPoint);
  requires $FrameCounts[$S] == 0;
  requires (forall i:int::{TV(i)} $toAbs[i] == NO_ABS);
  requires StaticInv($toAbs, $SectionMem, $SectionAbs);
  requires (forall i:int::{$PciConfigState[i]} $PciConfigState[i] == 0);
  requires (forall i:int::{$IoMmuState[i]} $IoMmuState[i] == 0);
  requires !$IomFrozen && !$IoMmuEnabled;
  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies $MemVars, AllGcVars, $toAbs;
  modifies $IdtMem, $IdtMemOk, $IdtOk;
  modifies $IomMem, $IomFrozen, $IoMmuEnabled, $IoMmuState, DmaAddr;
  modifies $TimerSeq, $TimerFreq, $PicSeq;
  modifies StackCheck;
  ensures  StaticInv($toAbs, $SectionMem, $SectionAbs);
  ensures  NucleusInv($S, $StackState[$S := StackRunning], $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  ensures  WellFormed($toAbs);
  ensures  StackCheckInv($S, StackCheck);
  ensures  esp == StackHi($S) - 4;
  ensures  Aligned(esp);
  ensures  ebp == 0; // end of frame pointer linked list
  ensures  $IdtOk; // note: once the interrupt table is set, it stays set
  ensures  PicOk($PicSeq);
  ensures  TimerOk($TimerSeq) && $TimerFreq == 0;

procedure FaultHandler($_stackState:[int]StackState, $ebp:int, $esp:int, $eip:int);
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp) && word(esp);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires SpRequire($S, esp, 12);
  requires $_stackState == $StackState[$S := StackEmpty][?InterruptStack := StackRunning];
  requires (StackStateTag($StackState[?InterruptStack]) == ?STACK_YIELDED ==>
               $RET == ReturnToAddr($eip)
            && $StackState[?InterruptStack] == StackYielded($ebp, $esp, $eip));
  modifies $Eip, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies AllGcVars, $MemVars;
  modifies StackCheck;
  ensures  StackCheckInv(?InterruptStack, StackCheck);
  ensures  (StackStateTag($StackState[?InterruptStack]) == ?STACK_YIELDED ==>
               NucleusInv(?InterruptStack, $_stackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars)
            && ebp == $ebp
            && esp == $esp);

procedure ErrorHandler($_stackState:[int]StackState, $ebp:int, $esp:int, $eip:int);
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp) && word(esp);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires SpRequire($S, esp, 16);
  requires $_stackState == $StackState[$S := StackEmpty][?InterruptStack := StackRunning];
  requires (StackStateTag($StackState[?InterruptStack]) == ?STACK_YIELDED ==>
               $RET == ReturnToAddr($eip)
            && $StackState[?InterruptStack] == StackYielded($ebp, $esp, $eip));
  modifies $Eip, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies AllGcVars, $MemVars;
  modifies StackCheck;
  ensures  StackCheckInv(?InterruptStack, StackCheck);
  ensures  (StackStateTag($StackState[?InterruptStack]) == ?STACK_YIELDED ==>
               NucleusInv(?InterruptStack, $_stackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars)
            && ebp == $ebp
            && esp == $esp);

procedure InterruptHandler($_stackState:[int]StackState, $ebp:int, $esp:int, $eip:int);
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp) && word(esp);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires SpRequire($S, esp, 12);
  requires $_stackState == $StackState
              [$S := StackInterrupted(eax, ebx, ecx, edx, esi, edi, ebp, esp + 12, $Mem[esp], $Mem[esp + 4], $Mem[esp + 8])]
              [?InterruptStack := StackRunning];
  requires (StackStateTag($StackState[?InterruptStack]) == ?STACK_YIELDED ==>
               $RET == ReturnToAddr($eip)
            && $StackState[?InterruptStack] == StackYielded($ebp, $esp, $eip));
  modifies $Eip, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies AllGcVars, $MemVars;
  modifies StackCheck;
  ensures  StackCheckInv(?InterruptStack, StackCheck);
  ensures  (StackStateTag($StackState[?InterruptStack]) == ?STACK_YIELDED ==>
               NucleusInv(?InterruptStack, $_stackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars)
            && ebp == $ebp
            && esp == $esp);

procedure FatalHandler();
  modifies $Eip, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures false;

// TODO: better dispatcher
procedure Throw($_stackState:[int]StackState, $ebp:int, $esp:int, $eip:int);
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp) && word(esp);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires SpRequire($S, esp, 4);
  requires $_stackState == $StackState[$S := StackEmpty][?InterruptStack := StackRunning];
  requires (StackStateTag($StackState[?InterruptStack]) == ?STACK_YIELDED ==>
               $RET == ReturnToAddr($eip)
            && $StackState[?InterruptStack] == StackYielded($ebp, $esp, $eip));
  modifies $Eip, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies AllGcVars, $MemVars;
  modifies StackCheck;
  ensures  StackCheckInv(?InterruptStack, StackCheck);
  ensures  (StackStateTag($StackState[?InterruptStack]) == ?STACK_YIELDED ==>
               NucleusInv(?InterruptStack, $_stackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars)
            && ebp == $ebp
            && esp == $esp);

procedure GetStackState($s:int);
  requires word(ecx);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires ecx == $s;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires ReturnToAddr($Mem[esp]) == $RET;
  requires SpRequire($S, esp, 4);
  modifies $Eip, eax, ecx, edx, esp;
  ensures  NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  ensures  eax == StackStateTag($StackState[$s]);
  ensures  ebp == old(ebp);
  ensures  esp == old(esp) + 4;

procedure ResetStack($s:int);
  requires word(ecx);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires ecx == $s;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires ScanStackInv($S, $Mem, $FrameVars, $Mem[esp], esp, ebp);
  requires $StackState[$s] != StackRunning ==> ReturnToAddr($Mem[esp]) == $RET;
  requires SpRequire($S, esp, 4);
  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies AllGcVars, $MemVars;
  ensures  NucleusInv($S, $StackState[$s := StackEmpty], $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  ensures  ebp == old(ebp);
  ensures  esp == old(esp) + 4;

// extern static void YieldTo(uint stackId);
// Switch to a stack $s.
//   - $s may be empty, yielded, interrupted, or the current running stack.
// Change the state of $S to yielded, then change the state of $s to running.
procedure YieldTo($s:int, $_stackState:[int]StackState,
            $eax:int, $ebx:int, $ecx:int, $edx:int, $esi:int, $edi:int, $ebp:int, $esp:int,
            $eip:int, $cs:int, $efl:int);
  requires ecx == $s;
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires isStack($S) && $StackState[$S] == StackRunning;
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  requires ScanStackInv($S, $Mem, $FrameVars, $Mem[esp], esp, ebp);
  requires SpRequire($S, esp, 4);
  requires $_stackState == $StackState[$S := StackYielded(ebp, esp + 4, $Mem[esp])][$s := StackRunning];
  requires ($StackState[$s] == StackRunning && $s == $S && $RET == ReturnToAddr($Mem[esp]))
        || ($StackState[$s] == StackYielded($ebp, $esp, $eip) && $RET == ReturnToAddr($eip))
        || ($StackState[$s] == StackInterrupted($eax, $ebx, $ecx, $edx, $esi, $edi, $ebp, $esp, $eip, $cs, $efl)
            && $RET == ReturnToInterrupted($eip, $cs, $efl))
        || ($StackState[$s] == StackEmpty && $RET == ReturnToAddr(?KernelEntryPoint)
            && $FrameCounts[$s] == 0);

  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  modifies AllGcVars, $MemVars;
  modifies StackCheck;

  ensures  StackCheckInv($s, StackCheck);
  ensures  ($StackState[$s] == StackRunning ==>
               NucleusInv($s, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars)
            && ebp == old(ebp)
            && esp == old(esp) + 4);
  ensures  ($StackState[$s] == StackYielded($ebp, $esp, $eip) ==>
               NucleusInv($s, $_stackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars)
            && ebp == $ebp
            && esp == $esp);
  ensures  ($StackState[$s] == StackInterrupted($eax, $ebx, $ecx, $edx, $esi, $edi, $ebp, $esp, $eip, $cs, $efl) ==>
               NucleusInv($s, $_stackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars)
            && ebp == $ebp
            && esp == $esp
            && eax == $eax && ebx == $ebx && ecx == $ecx && edx == $edx && esi == $esi && edi == $edi);
  ensures  ($StackState[$s] == StackEmpty ==>
               NucleusInv($s, $_stackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars)
            && esp == StackHi($s) - 4
            && ebp == 0 // end of frame pointer linked list
            );

// extern static void VgaTextWrite(uint screenOffset, uint hexMessage);
procedure VgaTextWrite();
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires $RET == ReturnToAddr($Mem[esp]);
  requires SpRequire($S, esp, 4);
  modifies $Eip, esp;
  modifies $VgaNextEvent, $VgaEvents;
  ensures  ecx < 4000 ==>
               $VgaNextEvent == old($VgaNextEvent) + 1
            && $VgaEvents == old($VgaEvents)[old($VgaNextEvent) := VgaTextStore(?VgaTextLo + 2 * ecx, edx)];
  ensures  esp == old(esp) + 4;

// extern static uint TryReadKeyboard();
procedure TryReadKeyboard();
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires $RET == ReturnToAddr($Mem[esp]);
  requires SpRequire($S, esp, 4);
  modifies $Eip, eax, esp;
  modifies $KeyboardAvailable, $KeyboardDone;
  ensures  $KeyboardAvailable == old($KeyboardDone) ==> eax == 256;
  ensures  $KeyboardAvailable >  old($KeyboardDone) ==> eax == $KeyboardEvents[old($KeyboardDone)];
  ensures  esp == old(esp) + 4;

// extern static uint StartTimer(uint freq);
procedure StartTimer();
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires $RET == ReturnToAddr($Mem[esp]);
  requires SpRequire($S, esp, 4);
  modifies $Eip, eax, esp;
  modifies $TimerSeq, $TimerFreq;
  ensures  TimerOk($TimerSeq) && $TimerFreq == old(ecx);
  ensures  esp == old(esp) + 4;

// extern static void SendEoi();
procedure SendEoi();
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires $RET == ReturnToAddr($Mem[esp]);
  requires SpRequire($S, esp, 4);
  requires PicOk($PicSeq);
  modifies $Eip, eax, edx, esp;
  modifies $PicSeq;
  ensures  $PicSeq[0] == old($PicSeq[0]) + 1;
  ensures  $PicSeq[1] == old($PicSeq[1]) + 1;
  ensures  esp == old(esp) + 4;

// extern static uint PciConfigRead32(uint id, uint offset);
procedure PciConfigRead32();
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires $RET == ReturnToAddr($Mem[esp]);
  requires SpRequire($S, esp, 4);
  modifies $Eip, eax, ecx, edx, esp;
  modifies $PciConfigId, $PciConfigOffset;
  ensures  esp == old(esp) + 4;
  ensures  PciConfigReadResult(old(ecx), old(edx), eax);

// extern static uint PciMemSetup(uint id);
procedure PciMemSetup();
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires $RET == ReturnToAddr($Mem[esp]);
  requires isStack($S) && SpRequire($S, esp, 4);
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, esp; // not ebp
  modifies $Mem, $pciMem;
  modifies $PciConfigId, $PciConfigOffset, $PciConfigState;
  ensures  esp == old(esp) + 4;
  ensures  eax == PciMemSize(old(ecx));
  ensures  NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);

// internal extern static byte[] PciDmaBuffer();
procedure PciDmaBuffer();
  requires $RET == ReturnToAddr($Mem[esp]);
  requires isStack($S) && SpRequire($S, esp, 4);
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  modifies $Eip, eax, edx, esp;
  ensures  esp == old(esp) + 4;
  ensures  $IoMmuEnabled ==> eax == ?dmaLo - 8;
  ensures  !$IoMmuEnabled ==> eax == 0;

// internal extern static uint PciDmaPhysicalAddr();
procedure PciDmaPhysicalAddr();
  requires $RET == ReturnToAddr($Mem[esp]);
  requires isStack($S) && SpRequire($S, esp, 4);
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  modifies $Eip, eax, edx, esp;
  ensures  esp == old(esp) + 4;
  ensures  $IoMmuEnabled ==> eax == ?dmaLo;
  ensures  !$IoMmuEnabled ==> eax == 0;

// internal extern static uint PciMemRead32(uint id, uint offset);
procedure PciMemRead32($id:int, $offset:int);
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires ecx == $id;
  requires edx == $offset;
  requires $RET == ReturnToAddr($Mem[esp]);
  requires isStack($S) && SpRequire($S, esp, 4);
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, esp; // not ebp
  ensures  esp == old(esp) + 4;
  ensures  PciMemLoaded($id, PciMemAddr($id) + $offset, eax);

// internal extern static void PciMemWrite32(uint id, uint offset, uint val);
procedure PciMemWrite32($id:int, $offset:int, $val:int);
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires ecx == $id;
  requires edx == $offset;
  requires $FrameSlices[$S][esp + 4] == $FrameCounts[$S] && $fMems[$S][esp + 4] == $val;
  requires $RET == ReturnToAddr($Mem[esp]);
  requires isStack($S) && SpRequire($S, esp, 8);
  requires NucleusInv($S, $StackState, $toAbs, $AbsMem, GcVars, $MemVars, $FrameVars, $IoVars);
  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, esp; // not ebp
  ensures  esp == old(esp) + 4;
  ensures  PciMemStored($id, PciMemAddr($id) + $offset, $val);

// extern static long Rdtsc();
procedure CycleCounter();
  requires $RET == ReturnToAddr($Mem[esp]);
  requires SpRequire($S, esp, 4);
  modifies $Eip, eax, edx, esp;
  ensures  esp == old(esp) + 4;

// extern static void DebugPrintHex(uint screenOffset, uint hexMessage);
procedure DebugPrintHex();
  requires word(eax) && word(ebx) && word(ecx) && word(edx) && word(esi) && word(edi) && word(ebp);
  requires $RET == ReturnToAddr($Mem[esp]);
  requires SpRequire($S, esp, 4);
  modifies $Eip, $RET, eax, ebx, ecx, edx, esi, edi, esp; // not ebp
  ensures  esp == old(esp) + 4;


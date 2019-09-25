//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

//////////////////////////////////////////////////////////////////////////////
// STACKS
//////////////////////////////////////////////////////////////////////////////

// Stack identifiers are numbered 0, 1, 2, ..., ?NumStacks - 1
const ?NumStacks:int; axiom ?NumStacks == 64;
const ?InitialStack:int; axiom ?InitialStack == 0;
const ?InterruptStack:int; axiom ?InterruptStack == 0;

var $S:int; // current stack id

// Each managed stack $s grows from StackHi($s) down to StackLo($s)
//   (see Gc_i.beat)

// Managed code can only write to the stack from an address StackLo($s) <= i < StackHi($s).
// --> This includes writes caused by calls and interrupts!
// A call consumes 4 bytes of stack space.
// An interrupt can consume as much as ?InterruptReserve bytes of stack space.
// Thus, the managed code should never allow esp < StackLo($s) + ?InterruptReserve
// when interrupts are enabled or when traps (e.g. null pointer or divide-by-zero traps)
// are possible.

// The managed code can enforce this with run-time checks against StackCheck:
//   If StackCheck <= esp, then there at least ?StackReserve + ?InterruptReserve
// bytes are available below esp.
// When managed code calls the Nucleus, it must guarantee that
//   StackLo($s) <= esp
// holds after the call instruction.
// (So before the call, StackLo($s) + 4 <= esp.)
// When the Nucleus returns to native code, it restores the esp before the call.

const ?InterruptReserve:int; axiom ?InterruptReserve == 16;
const ?StackReserve:int; axiom ?StackReserve == 4096;
var StackCheck:int;

// Each stack can be in one of four states:
//   - empty
//   - running
//   - yielded(ebp, esp, eip)
//   - interrupted(eax, ebx, ecx, edx, esi, edi, ebp, esp, eip, cs, eflags)
// The arguments to yielded and interrupted are the registers that must
// be restored to resume the thread.  (For example, to restore yielded(b, s, i),
// one might set ebp == b, esp == s - 4, $Mem[esp] == i, and then invoke "ret").
type StackState;
var $StackState:[int]StackState;
const StackEmpty:StackState;
const StackRunning:StackState;
function StackYielded($ebp:int, $esp:int, $eip:int) returns(StackState);
function StackInterrupted($eax:int, $ebx:int, $ecx:int, $edx:int, $esi:int, $edi:int, $ebp:int, $esp:int, $eip:int, $cs:int, $efl:int) returns(StackState);

// The four stack states are distinct:
const ?STACK_EMPTY:int; axiom ?STACK_EMPTY == 0;
const ?STACK_RUNNING:int; axiom ?STACK_RUNNING == 1;
const ?STACK_YIELDED:int; axiom ?STACK_YIELDED == 2;
const ?STACK_INTERRUPTED:int; axiom ?STACK_INTERRUPTED == 3;
function StackStateTag(state:StackState) returns(int);
function IsStackStateTag(tag:int) returns(bool) { 0 <= tag && tag <= 3 }
function IsStackStateTagFor(tag:int, state:StackState) returns(bool) { IsStackStateTag(tag) && tag == StackStateTag(state) }

// To switch to an StackEmpty stack $s, the stack memory must contain one word:
//   StackHi($s) - 8: managedEntryPoint
// Execution begins by returning to the managedEntryPoint.  This entry point
// should never return.  (This is enforced by the TAL checker.)
const ?KernelEntryPoint:int;


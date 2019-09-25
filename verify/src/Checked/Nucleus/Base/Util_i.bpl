// Write hex digit (ecx & 15) to screen offset edx
procedure writeHexDigit();
  requires 0 <= edx && edx <= 160 - 2;
  modifies $Eip, ecx;

// Write value eax to screen offset edx
procedure writeHex();
  requires 0 <= edx && edx <= 160 - 16;
  modifies $Eip, eax, ecx, edx;

procedure debugBreak();
  modifies $Eip, eax, ecx, edx;
  ensures false;

procedure DebugBreak();
  modifies $Eip, eax, ecx, edx, esp;
  ensures false;

function MapStacksToMem($Mem:[int]int) returns([int][int]int);
axiom (forall $Mem:[int]int, s:int, i:int::{MapStacksToMem($Mem)[s][i]} MapStacksToMem($Mem)[s][i] == $Mem[i]);


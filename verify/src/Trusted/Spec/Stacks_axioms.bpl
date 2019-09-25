//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

axiom (StackStateTag(StackEmpty) == ?STACK_EMPTY);
axiom (StackStateTag(StackRunning) == ?STACK_RUNNING);
axiom (forall $ebp:int, $esp:int, $eip:int::{StackYielded($ebp, $esp, $eip)} StackStateTag(StackYielded($ebp, $esp, $eip)) == ?STACK_YIELDED);
axiom (forall $eax:int, $ebx:int, $ecx:int, $edx:int, $esi:int, $edi:int, $ebp:int, $esp:int, $eip:int, $cs:int, $efl:int::
        {StackInterrupted($eax, $ebx, $ecx, $edx, $esi, $edi, $ebp, $esp, $eip, $cs, $efl)}
         StackStateTag(StackInterrupted($eax, $ebx, $ecx, $edx, $esi, $edi, $ebp, $esp, $eip, $cs, $efl)) == ?STACK_INTERRUPTED);

axiom (forall $ebp1:int, $esp1:int, $eip1:int,
              $ebp2:int, $esp2:int, $eip2:int
            ::{StackYielded($ebp1, $esp1, $eip1),
               StackYielded($ebp2, $esp2, $eip2)}
               StackYielded($ebp1, $esp1, $eip1)
            == StackYielded($ebp2, $esp2, $eip2) ==>
            $ebp1 == $ebp2 && $esp1 == $esp2 && $eip1 == $eip2);

axiom (forall $eax1:int, $ebx1:int, $ecx1:int, $edx1:int, $esi1:int, $edi1:int, $ebp1:int, $esp1:int, $eip1:int, $cs1:int, $efl1:int,
              $eax2:int, $ebx2:int, $ecx2:int, $edx2:int, $esi2:int, $edi2:int, $ebp2:int, $esp2:int, $eip2:int, $cs2:int, $efl2:int
            ::{StackInterrupted($eax1, $ebx1, $ecx1, $edx1, $esi1, $edi1, $ebp1, $esp1, $eip1, $cs1, $efl1),
               StackInterrupted($eax2, $ebx2, $ecx2, $edx2, $esi2, $edi2, $ebp2, $esp2, $eip2, $cs2, $efl2)}
               StackInterrupted($eax1, $ebx1, $ecx1, $edx1, $esi1, $edi1, $ebp1, $esp1, $eip1, $cs1, $efl1)
            == StackInterrupted($eax2, $ebx2, $ecx2, $edx2, $esi2, $edi2, $ebp2, $esp2, $eip2, $cs2, $efl2) ==>
            $eax1 == $eax2 && $ebx1 == $ebx2 && $ecx1 == $ecx2 && $edx1 == $edx2 && $esi1 == $esi2 && $edi1 == $edi2 &&
            $ebp1 == $ebp2 && $esp1 == $esp2 && $eip1 == $eip2 && $cs1 == $cs2 && $efl1 == $efl2);

axiom word(?KernelEntryPoint);

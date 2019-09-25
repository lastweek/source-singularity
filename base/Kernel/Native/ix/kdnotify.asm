;; ----------------------------------------------------------------------------
;;
;;  Copyright (c) Microsoft Corporation.  All rights reserved.
;;
;; ----------------------------------------------------------------------------

include hal.inc

SYMFIX(?KdNotifyTrap@@YIXPAUKdDebugTrapData@@@Z) proc

        nop
        mov     PAX, PCX
        int     29
        ret

SYMFIX(?KdNotifyTrap@@YIXPAUKdDebugTrapData@@@Z) endp

        
SYMFIX(?KdNotifyException@@YIXPAUClass_System_Exception@@I@Z) proc
        GET_PROCESSOR_CONTEXT PAX
        mov [PAX].Struct_Microsoft_Singularity_ProcessorContext._exception, PCX
        mov PAX, PDX
        int 29                          ;Notify debugging stub of first chance exception.
        ret
SYMFIX(?KdNotifyException@@YIXPAUClass_System_Exception@@I@Z) endp

end


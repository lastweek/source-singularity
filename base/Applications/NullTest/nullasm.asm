; 
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

ifdef SINGULARITY
.686p
.mmx
.xmm
else ;; SINGULARITY
.686
endif ;; SINGULARITY

.model flat
.code

ifdef SINGULARITY
assume ds:flat
assume es:flat
assume ss:flat
assume fs:nothing
assume gs:nothing
else ;; SINGULARITY
EXCLUDED equ 0
SINGLE_THREADED equ 0
endif ;; SINGULARITY


        align       16

??_7System_VTable@@6B@ proc
        ;; const System_VTable::`vftable'
        int 3
??_7System_VTable@@6B@ endp

??_7System_RuntimeType@@6B@ proc        
        ;; const System_RuntimeType::`vftable'
        int 3
??_7System_RuntimeType@@6B@ endp

end

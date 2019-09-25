;
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

.code

include hal.inc
IRC_CHOP  equ      0c00h ; chop

;;;__declspec(naked) uint16 __fastcall g_ClearFp()
?g_ClearFp@@YAGXZ proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog

        ;;// Save the old SW
        fnstsw [esp-4];
        fnclex
        mov eax, [esp-4];
        and eax, 0ffffh;

        pop rbp;
        ret; // Returns result in EAX
?g_ClearFp@@YAGXZ endp 

;;;__declspec(naked) uint16 __fastcall g_ControlFp(uint16 newctrl, uint16 mask)
?g_ControlFp@@YAGGG@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog

        ;;// Save the old CW
        fstcw [esp-4];
        mov eax, [esp-4];
        and eax, 0ffffh;

        ;;// Load the new CW
        and ecx,edx;
        not edx;
        and edx,eax;
        or  edx,ecx;
        mov [esp-4], edx;
        fldcw [esp-4];

        pop rbp
        ret;
?g_ControlFp@@YAGGG@Z endp

;;;__declspec(naked) void __fastcall g_RestoreFp(uint16 newctrl)
?g_RestoreFp@@YAXG@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog

        ;;// Load the new CW
        and ecx, 0ffffh;
        mov [esp-4], ecx;
        fldcw [esp-4];

        pop rbp
        ret;
?g_RestoreFp@@YAXG@Z endp

ifdef GARBAGE 

;;;static float64 __fastcall _frnd(float64 v)
?_frnd@@YANN@Z PROC frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        
        fld QWORD PTR [rsp +8];
        frndint;
        pop rbp;
        ret
?_frnd@@YANN@Z endp

;;;static int32 __fastcall _ftoi(float64 v)
?_ftoi@@YAHN@Z PROC frame 
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
ifdef NYI
        sub rsp, 24;  
        ;;int32 intval; +0  
        ;;int32 oldcw;  +8
        ;;int32 newcw;  +16
        
        fstcw  DWORD PTR [rsp+8] ;      // get control word

        mov eax, r9d;   // round mode saved
        or  eax,;  // set chop rounding mode
        mov r10d, eax;   // back to memory

        fldcw r10d;      // reset rounding
        fld rcx;
        fistp r8d;      // store chopped integer
        fwait;
        fldcw r9d;      // restore rounding
        
        add rsp, 24
endif        
        or  rax,rax
        mov eax,r9d
        pop rbp;
        ret
?_ftoi@@YAHN@Z endp 

;;;float64 Class_System_Math::g_Log(float64 v)
?g_Log@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld QWORD PTR [rsp +8];
        fldln2;
        fxch ST(1);
        fyl2x; // Returns result in ST(0)
        pop rbp;
        ret
?g_Log@Class_System_Math@@SANN@Z endp

;;;float64 Class_System_Math::g_Sin(float64 v)
?g_Sin@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld QWORD PTR [rsp +8];
        fsin; // Returns result in ST(0)
        pop rbp;
        ret
?g_Sin@Class_System_Math@@SANN@Z endp 

;;;float64 Class_System_Math::g_Cos(float64 v)
?g_Cos@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld QWORD PTR [rsp +8];
        fcos; // Returns result in ST(0)
        pop rbp;
        ret
?g_Cos@Class_System_Math@@SANN@Z endp

;;;float64 Class_System_Math::g_Tan(float64 v)
?g_Tan@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld QWORD PTR [rsp +8];
        fptan;
        fstp ST(0); // Returns result in ST(0)
        pop rbp;
        ret
?g_Tan@Class_System_Math@@SANN@Z endp

;;;float64 Class_System_Math::g_Atan(float64 v)
?g_Atan@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld QWORD PTR [rsp +8];
        fld1;
        fpatan;
        pop rbp;
        ret
?g_Atan@Class_System_Math@@SANN@Z endp  

endif 
;;;float64 Class_System_Math::g_Atan2(float64 v, float64 w)
?g_Atan2@Class_System_Math@@SANNN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld QWORD PTR [rsp +8];
        fld QWORD PTR [rsp +16];
        fpatan;
        pop rbp;
        ret
?g_Atan2@Class_System_Math@@SANNN@Z endp

;;;float64 Class_System_Math::g_Abs(float64 v)
?g_Abs@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld QWORD PTR [rsp +8];
        fabs;
        pop rbp
        ret
?g_Abs@Class_System_Math@@SANN@Z endp

;;;float64 Class_System_Math::g_Sqrt(float64 v)
?g_Sqrt@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld QWORD PTR [rsp +8];
        fsqrt;
        pop rbp;
        ret
?g_Sqrt@Class_System_Math@@SANN@Z endp


;;;float64 Class_System_Math::g_Log10(float64 v)
?g_Log10@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld QWORD PTR [rsp +8];
        fldlg2;
        fxch ST(1);
        fyl2x; // Returns result in ST(0)
        pop rbp;
        ret
?g_Log10@Class_System_Math@@SANN@Z endp
 
;;;float64 Class_System_Math::g_Exp(float64 v)
?g_Exp@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fldl2e;
        fmul QWORD PTR [rsp +8];
        fld ST(0);
        frndint;
        fxch ST(1);
        fsub ST(0), ST(1);
        f2xm1;
        fld1;
        faddp ST(1), ST(0);
        fscale;
        fstp ST(1); // Returns result in ST(0)
        pop rbp;
        ret
?g_Exp@Class_System_Math@@SANN@Z endp

;;;float64 Class_System_Math::g_Acos(float64 v)
?g_Acos@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld  real8 PTR [rsp+8] ;
        fld1;               // load 1.0
        fadd st, st(1);     // 1+x
        fld1;               // load 1.0
        fsub st, st(2);     // 1-x
        fmul;               // (1+x)(1-x)
        fsqrt;              // sqrt((1+x)(1-x))
        fxch;
        fpatan;             // fpatan(x,sqrt((1+x)(1-x)))
        pop rbp;
        ret
?g_Acos@Class_System_Math@@SANN@Z endp

;;;float64 Class_System_Math::g_Asin(float64 v)
?g_Asin@Class_System_Math@@SANN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fld  real8 PTR [rsp+8] ;
        fld1;               // load 1.0
        fadd st, st(1);     // 1+x
        fld1;               // load 1.0
        fsub st, st(2);     // 1-x
        fmul;               // (1+x)(1-x)
        fsqrt;              // sqrt((1+x)(1-x))
        fpatan;             // fpatan(x,sqrt((1+x)(1-x)))
        pop rbp;
        ret
?g_Asin@Class_System_Math@@SANN@Z endp

;;;static float64 _fastpow(float64 v, float64 w)
?g_Pow@Class_System_Math@@SANNN@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        ;;fld w;              // neither v or w can be a boundary cases.
        ;;fld v;
        fld  real8 PTR [rsp+16] ;
        fld  real8 PTR [rsp+8] ;
        fyl2x;              // compute y*log2(x)
        fld st(0);          // duplicate stack top
        frndint;            // N = round(y)
        fsubr st(1), st;
        fxch;   
        fchs;               // g = y - N where abs(g) < 1
        f2xm1;              // 2**g - 1
        fld1;
        fadd;               // 2**g
        fscale;             // (2**g) * (2**N) - gives 2**y
        fstp st(1);         // pop extra stuff from fp stack
        pop rbp;
        ret
?g_Pow@Class_System_Math@@SANNN@Z endp

end
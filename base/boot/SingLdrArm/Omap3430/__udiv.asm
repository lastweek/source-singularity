;
; Copyright (c) Microsoft Corporation.  All rights reserved.
;

; Unsigned divide of r1 by r0: returns quotient in r0, remainder in r1
; Destroys a3, a4

 ;   IMPORT __rt_div0

    AREA   |.text|, CODE, READONLY

	EXPORT |__rt_udiv| [FUNC]

|__rt_udiv|

    MOV     a4, #0
    MOVS    a3, r0
    BEQ     DivideByZero

while
    CMP     a3, r1, LSR #8
    MOVLS   a3, a3, LSL #8
    BLO     while

    CMP     a3, r1, LSR #1
    BHI     goto7
    CMP     a3, r1, LSR #2
    BHI     goto6
    CMP     a3, r1, LSR #3
    BHI     goto5
    CMP     a3, r1, LSR #4
    BHI     goto4
    CMP     a3, r1, LSR #5
    BHI     goto3
    CMP     a3, r1, LSR #6
    BHI     goto2
    CMP     a3, r1, LSR #7
    BHI     goto1
loop
    MOVHI   a3, a3, LSR #8

    CMP     r1, a3, LSL #7
    ADC     a4, a4, a4
    SUBCS   r1, r1, a3, LSL #7
    CMP     r1, a3, LSL #6

goto1
    ADC     a4, a4, a4
    SUBCS   r1, r1, a3, LSL #6
    CMP     r1, a3, LSL #5

goto2
    ADC     a4, a4, a4
    SUBCS   r1, r1, a3, LSL #5
    CMP     r1, a3, LSL #4

goto3
    ADC     a4, a4, a4
    SUBCS   r1, r1, a3, LSL #4
    CMP     r1, a3, LSL #3

goto4
    ADC     a4, a4, a4
    SUBCS   r1, r1, a3, LSL #3
    CMP     r1, a3, LSL #2

goto5
    ADC     a4, a4, a4
    SUBCS   r1, r1, a3, LSL #2
    CMP     r1, a3, LSL #1

goto6
    ADC     a4, a4, a4
    SUBCS   r1, r1, a3, LSL #1

goto7
    CMP     r1, a3
    ADC     a4, a4, a4
    SUBCS   r1, r1, a3
    CMP     a3, r0
    BNE     loop
    MOV     r0, a4

end
    MOV	    pc, lr


;
;   Divide by zero has occurred. Raise an exception
;   call RaiseException(STATUS_INTEGER_DIVIDE_BY_ZERO, 0, 0, NULL)
;

DivideByZero

    ldr     r0, =0xFFFFFFFF
    mov     r1, r0
    mov     pc, r12

    END

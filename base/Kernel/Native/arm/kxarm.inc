;
; Copyright (c) Microsoft Corporation.  All rights reserved.
;
;++
;
;
; Module Name:
;
;    kxarm.h
;
; Abstract:
;
;    This is an implementation of the WINCE/ARM Calling Sequence
;    Specification.
;
; Environment:
;    String Library
;
; Revision History:
;--

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TODO:  No Thumbing or Interworking for now.
;
         GBLL   Thumbing
Thumbing SETL   {FALSE}
         GBLL   Interworking
Interworking SETL   {FALSE}
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
               
		GBLS    VBar
VBar	SETS    "|"
		GBLL	HaveExceptHandler
		GBLS	AreaName
		GBLS	FuncName
		GBLS	PrologName
		GBLS	FuncEndName
		GBLS	ExceptHandler
		GBLS	ExceptData
AreaName SETS	"|.text|"
HaveExceptHandler SETL {FALSE}

	MACRO
	TEXTAREA
	AREA |.text|,ALIGN=2,CODE,READONLY
AreaName SETS "|.text|"
	MEND

    MACRO
    THUMBAREA
    AREA |.text|,ALIGN=2,CODE,READONLY,THUMB
AreaName SETS "|.text|"
    MEND

	MACRO
	STARTUPTEXT
	AREA |.astart|,ALIGN=2,CODE
AreaName SETS "|.astart|"
	MEND

	MACRO
	START_REGION	$NameBegin
	LCLS    TempName
TempName SETS    VBar:CC:"$NameBegin":CC:VBar
	EXPORT	$TempName[DATA]
$TempName
	MEND

	MACRO
	END_REGION		$NameEnd
	LCLS    TempName
TempName SETS    VBar:CC:"$NameEnd":CC:VBar
	EXPORT	$TempName[DATA]
$TempName
	MEND

;
;   This macro should be used if the assembly function is in ARM
;

	MACRO
	NESTED_ARMENTRY	$Name
FuncName    SETS    VBar:CC:"$Name":CC:VBar
PrologName  SETS    VBar:CC:"$Name":CC:"_Prolog":CC:VBar
FuncEndName SETS    VBar:CC:"$Name":CC:"_end":CC:VBar
	LCLS	ExceptBit
	IF HaveExceptHandler
ExceptBit   SETS	"0x80000000"
	ELSE
ExceptBit   SETS	"0"
	ENDIF

	AREA |.pdata|,ALIGN=2,PDATA
	DCD	    $FuncName
    DCD     (($PrologName-$FuncName)/4) :OR: ((($FuncEndName-$FuncName)/4):SHL:8) :OR: 0x40000000 :OR: $ExceptBit
	AREA $AreaName,CODE,READONLY
	ALIGN	2
	EXPORT	$FuncName [FUNC]
	IF HaveExceptHandler
    DCD $ExceptHandler
    DCD $ExceptData
HaveExceptHandler SETL {FALSE}
	ENDIF
$FuncName
	ROUT
	MEND

;
;   This macro should be used if the assembly function is in THUMB
;
	MACRO
	NESTED_THUMBENTRY	$Name
FuncName    SETS    VBar:CC:"$Name":CC:VBar
PrologName  SETS    VBar:CC:"$Name":CC:"_Prolog":CC:VBar
FuncEndName SETS    VBar:CC:"$Name":CC:"_end":CC:VBar
	LCLS	ExceptBit
	IF HaveExceptHandler
ExceptBit   SETS	"0x80000000"
	ELSE
ExceptBit   SETS	"0"
	ENDIF

	AREA |.pdata|,ALIGN=2,PDATA
	DCD	    $FuncName
    DCD     (($PrologName-$FuncName)/2) :OR: ((($FuncEndName-$FuncName)/2):SHL:8) :OR: $ExceptBit
	AREA $AreaName,CODE,READONLY
	ALIGN	2
	EXPORT	$FuncName [FUNC]
	IF HaveExceptHandler
    DCD $ExceptHandler
    DCD $ExceptData
HaveExceptHandler SETL {FALSE}
	ENDIF
$FuncName
	ROUT
	MEND

;
;   This macro should be used if the assembly function is in ARM
;
	MACRO
	NESTED_ENTRY	$Name
FuncName    SETS    VBar:CC:"$Name":CC:VBar
PrologName  SETS    VBar:CC:"$Name":CC:"_Prolog":CC:VBar
FuncEndName SETS    VBar:CC:"$Name":CC:"_end":CC:VBar
	LCLS	ExceptBit
	IF HaveExceptHandler
ExceptBit   SETS	"0x80000000"
	ELSE
ExceptBit   SETS	"0"
	ENDIF

	AREA |.pdata|,ALIGN=2,PDATA
	DCD	    $FuncName
    DCD     (($PrologName-$FuncName)/4) :OR: ((($FuncEndName-$FuncName)/4):SHL:8) :OR: 0x40000000 :OR: $ExceptBit
	AREA $AreaName,CODE,READONLY
	ALIGN	2
	EXPORT	$FuncName [FUNC]
	IF HaveExceptHandler
    DCD $ExceptHandler
    DCD $ExceptData
HaveExceptHandler SETL {FALSE}
	ENDIF
$FuncName
	ROUT
	MEND

	MACRO
	PROLOG_END
$PrologName
	MEND

	MACRO
	LEAF_ENTRY	$Name
FuncName SETS    VBar:CC:"$Name":CC:VBar
PrologName SETS	"Invalid Prolog"
FuncEndName SETS    VBar:CC:"$Name":CC:"_end":CC:VBar
	ALIGN	2
	EXPORT	$FuncName [FUNC]
$FuncName
	ROUT
	MEND

	MACRO
	ALTERNATE_ENTRY	$Name
	LCLS    TempName
TempName SETS    VBar:CC:"$Name":CC:VBar
	EXPORT	$TempName [FUNC]
$TempName
	MEND

	MACRO
	ENTRY_END	$Name
$FuncEndName
	MEND

	MACRO
	NESTED_END	$Name
$FuncEndName
	MEND

	MACRO
	LEAF_END	$Name
$FuncEndName
	MEND

	MACRO
	EXCEPTION_HANDLER	$Handler
ExceptHandler SETS    VBar:CC:"$Handler":CC:VBar
ExceptData SETS "0"
HaveExceptHandler SETL {TRUE}
	MEND

	MACRO
	EXCEPTION_HANDLER_DATA	$Handler, $HandlerData
ExceptHandler SETS    VBar:CC:"$Handler":CC:VBar
ExceptData SETS    VBar:CC:"$HandlerData":CC:VBar
HaveExceptHandler SETL {TRUE}
	MEND

	MACRO
	EXCEPTION_HANDLER_MILLICODE	$Handler, $HandlerData
ExceptHandler SETS    "$Handler"
ExceptData SETS    "$HandlerData"
HaveExceptHandler SETL {TRUE}
	MEND

; MAGIC_ARM_MODE_SWITCH: MS has instead put this macro definition into
; the kernel file winceos\coreos\nk\kernel\arm\intrlock.s.  It is also
; defined in corelibc\crtw32\eh\arm\handler.s.  In M4, these duplicate
; definitions should be yanked and put here, in this common location.

	END


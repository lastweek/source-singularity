
//

//

//

//

//

//
//--

#include "bl.h"

#define ABS(X)                          (((X) < 0) ? (-(X)) : (X))

#define STRING_TOKEN_LONG               1
#define STRING_TOKEN_ULONG              2
#define STRING_TOKEN_ULONG_HEX          3
#define STRING_TOKEN_LONGLONG           4
#define STRING_TOKEN_ULONGLONG          5
#define STRING_TOKEN_ULONGLONG_HEX      6
#define STRING_TOKEN_PVOID              7
#define STRING_TOKEN_PCHAR              8
#define STRING_TOKEN_CHAR               9

CHAR
BlRtlConvertCharacterToUpperCase(
    CHAR C
    )


//

//

//

//

//

//

//
//--

{
    if ((C >= 'a') && (C <= 'z')) {

        return C + 'A' - 'a';
    }

    return C;
}

BOOLEAN
BlRtlParsePositiveDecimal(
    PCSTR String,
    PUINT32 Number,
    PUINT32 CharactersConsumed
    )


//

//

//

//

//

//

//
//

//


//
//--

{
    UINT32 Digit;
    UINT32 Index;
    UINT32 Temp;

    if ((String[0] < '0') || (String[0] > '9')) {

        return FALSE;
    }

    Index = 0;
    Temp = 0;

    for (;;) {

        if ((String[Index] < '0') || (String[Index] > '9')) {

            *Number = Temp;
            *CharactersConsumed = Index;
            return TRUE;
        }

        Digit = String[Index] - '0';

        if (((Temp * 10) + Digit) < Temp) {

            return FALSE;
        }

        Temp = (Temp * 10) + Digit;
        Index += 1;
    }
}

BOOLEAN
BlRtlParseTypeSpecifier(
    PCSTR String,
    PINT32 Width,
    PCHAR PadCharacter,
    PUINT8 TokenType,
    PUINT32 CharactersConsumed
    )


//

//

//

//

//

//

//

//

//
//

//


//
//--

{
    UINT32 Advance;
    BOOLEAN WidthPresent;
    UINT32 Index;
    BOOLEAN Minus;
    UINT32 WidthPositiveValue;
    BOOLEAN Zero;

    SATISFY_OVERZEALOUS_COMPILER(WidthPositiveValue = 0);

    //
    
    //

    if (String[0] != '%') {

        return FALSE;
    }

    Index = 1;

    //
    
    //

    Minus = FALSE;
    Zero = FALSE;

    for (;;) {

        if (String[Index] == '-') {

            if (Minus != FALSE) {

                return FALSE;
            }

            Minus = TRUE;
            Index += 1;

        } else if (String[Index] == '0') {

            if (Zero != FALSE) {

                return FALSE;
            }

            Zero = TRUE;
            Index += 1;

        } else {

            break;
        }
    }

    //
    
    //

    if ((Minus != FALSE) && (Zero != FALSE)) {

        return FALSE;
    }

    //
    
    //

    WidthPresent = ((String[Index] >= '1') && (String[Index] <= '9'));

    if (WidthPresent != FALSE) {

        if (BlRtlParsePositiveDecimal(&String[Index],
                                      &WidthPositiveValue,
                                      &Advance) == FALSE) {

            return FALSE;
        }

        Index += Advance;
    }

    //
    
    //

    if (((Minus != FALSE) || (Zero != FALSE)) && (WidthPresent == FALSE)) {

        return FALSE;
    }

    //
    
    //

    if (Zero != FALSE) {

        *PadCharacter = '0';

    } else {

        *PadCharacter = ' ';
    }

    //
    
    //

    if (WidthPresent == FALSE) {

        *Width = 0;

    } else if (Minus == FALSE) {

        *Width = (INT32) WidthPositiveValue;

    } else {

        *Width = -((INT32) WidthPositiveValue);
    }

    //
    
    //

    if (BlRtlEqualStringN(&String[Index], "d", 1) != FALSE) {

        *TokenType = STRING_TOKEN_LONG;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "u", 1) != FALSE) {

        *TokenType = STRING_TOKEN_ULONG;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "x", 1) != FALSE) {

        *TokenType = STRING_TOKEN_ULONG_HEX;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "I64d", 4) != FALSE) {

        *TokenType = STRING_TOKEN_LONGLONG;
        Index += 4;

    } else if (BlRtlEqualStringN(&String[Index], "I64u", 4) != FALSE) {

        *TokenType = STRING_TOKEN_ULONGLONG;
        Index += 4;

    } else if (BlRtlEqualStringN(&String[Index], "I64x", 4) != FALSE) {

        *TokenType = STRING_TOKEN_ULONGLONG_HEX;
        Index += 4;

    } else if (BlRtlEqualStringN(&String[Index], "p", 1) != FALSE) {

        *TokenType = STRING_TOKEN_PVOID;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "s", 1) != FALSE) {

        *TokenType = STRING_TOKEN_PCHAR;
        Index += 1;

    } else if (BlRtlEqualStringN(&String[Index], "c", 1) != FALSE) {

        *TokenType = STRING_TOKEN_CHAR;
        Index += 1;

    } else {

        return FALSE;
    }

    //
    
    //

    *CharactersConsumed = Index;

    return TRUE;
}

BOOLEAN
BlRtlFormatSignedDecimalLong(
    PCHAR Output,
    UINT32 OutputSize,
    INT32 Value,
    INT32 Width,
    PUINT32 CharactersConsumed
    )


//

//

//

//

//

//

//

//

//
//

//


//
//--

{
    UINT32 Index;
    UINT32 MinimumWidth;
    BOOLEAN Minus;
    UINT32 NumberWidth;
    UINT32 PadWidth;
    UINT32 Temp;

    //
    
    //

    Minus = (BOOLEAN) (Value < 0);

    //
    
    //

    Temp = ABS(Value);
    NumberWidth = 0;

    do {

        NumberWidth += 1;
        Temp = Temp / 10;

    } while (Temp > 0);

    if (Minus != FALSE) {

        NumberWidth += 1;
    }

    PadWidth = 0;
    MinimumWidth = ABS(Width);

    if (MinimumWidth > NumberWidth) {

        PadWidth = MinimumWidth - NumberWidth;
    }

    //
    
    //

    if ((NumberWidth + PadWidth) > OutputSize) {

        return FALSE;
    }

    Index = 0;

    //
    
    //

    if (Width > 0) {

        while (PadWidth > 0) {

            Output[Index] = ' ';
            Index += 1;
            PadWidth -= 1;
        }
    }

    //
    
    //

    Temp = ABS(Value);
    Index += NumberWidth;

    do {

        Index -= 1;
        Output[Index] = (CHAR) ('0' + (Temp % 10));
        Temp = Temp / 10;

    } while (Temp > 0);

    //
    
    //

    if (Minus != FALSE) {

        Index -= 1;
        Output[Index] = '-';
    }

    //
    
    //

    Index += NumberWidth;

    while (PadWidth > 0) {

        Output[Index] = ' ';
        Index += 1;
        PadWidth -= 1;
    }

    //
    
    //

    *CharactersConsumed = Index;

    return TRUE;
}

BOOLEAN
BlRtlFormatUnsignedLong(
    PCHAR Output,
    UINT32 OutputSize,
    UINT32 Value,
    UINT8 PadCharacter,
    INT32 Width,
    UINT32 Base,
    PUINT32 CharactersConsumed
    )


//

//

//

//

//

//

//

//

//

//

//
//

//


//
//--

{
    UINT32 Index;
    UINT32 MinimumWidth;
    UINT32 NumberWidth;
    UINT32 PadWidth;
    UINT32 Temp;

    if (Base == 0) {

        return FALSE;
    }

    //
    
    //

    Temp = Value;
    NumberWidth = 0;

    do {

        NumberWidth += 1;
        Temp = Temp / Base;

    } while (Temp > 0);

    PadWidth = 0;
    MinimumWidth = ABS(Width);

    if (MinimumWidth > NumberWidth) {

        PadWidth = MinimumWidth - NumberWidth;
    }

    //
    
    //

    if ((NumberWidth + PadWidth) > OutputSize) {

        return FALSE;
    }

    Index = 0;

    //
    
    //

    if (Width > 0) {

        while (PadWidth > 0) {

            Output[Index] = PadCharacter;
            Index += 1;
            PadWidth -= 1;
        }
    }

    //
    
    //

    Temp = Value;
    Index += NumberWidth;

    do {

        Index -= 1;

        switch (Base) {

            case 10: {

                Output[Index] = (CHAR) ('0' + (Temp % Base));
                break;
            }

            case 16: {

                if ((Temp % Base) < 10) {

                    Output[Index] = (CHAR) ('0' + (Temp % Base));

                } else {

                    Output[Index] = (CHAR) ('A' + (Temp % Base) - 10);
                }

                break;
            }

            default: {

                return FALSE;
            }
        }

        Temp = Temp / Base;

    } while (Temp > 0);

    //
    
    //

    Index += NumberWidth;

    while (PadWidth > 0) {

        Output[Index] = PadCharacter;
        Index += 1;
        PadWidth -= 1;
    }

    //
    
    //

    *CharactersConsumed = Index;

    return TRUE;
}

BOOLEAN
BlRtlFormatUnsignedLongLong(
    PCHAR Output,
    UINT32 OutputSize,
    UINT64 Value,
    UINT8 PadCharacter,
    INT32 Width,
    UINT32 Base,
    PUINT32 CharactersConsumed
    )


//

//

//

//

//

//

//

//

//

//

//
//

//


//
//--

{
    UINT32 Index;
    UINT32 MinimumWidth;
    UINT32 NumberWidth;
    UINT32 PadWidth;
    UINT64 Temp;

    if (Base == 0) {

        return FALSE;
    }

    //
    
    //

    Temp = Value;
    NumberWidth = 0;

    do {

        NumberWidth += 1;
        Temp = Temp / Base;

    } while (Temp > 0);

    PadWidth = 0;
    MinimumWidth = ABS(Width);

    if (MinimumWidth > NumberWidth) {

        PadWidth = MinimumWidth - NumberWidth;
    }

    //
    
    //

    if ((NumberWidth + PadWidth) > OutputSize) {

        return FALSE;
    }

    Index = 0;

    //
    
    //

    if (Width > 0) {

        while (PadWidth > 0) {

            Output[Index] = PadCharacter;
            Index += 1;
            PadWidth -= 1;
        }
    }

    //
    
    //

    Temp = Value;
    Index += NumberWidth;

    do {

        Index -= 1;

        switch (Base) {

            case 10: {

                Output[Index] = (CHAR) ('0' + (Temp % Base));
                break;
            }

            case 16: {

                if ((Temp % Base) < 10) {

                    Output[Index] = (CHAR) ('0' + (Temp % Base));

                } else {

                    Output[Index] = (CHAR) ('A' + (Temp % Base) - 10);
                }

                break;
            }

            default: {

                return FALSE;
            }
        }

        Temp = Temp / Base;

    } while (Temp > 0);

    //
    
    //

    Index += NumberWidth;

    while (PadWidth > 0) {

        Output[Index] = PadCharacter;
        Index += 1;
        PadWidth -= 1;
    }

    //
    
    //

    *CharactersConsumed = Index;

    return TRUE;
}

UINT32
BlRtlStringLength(
    PCSTR String
    )


//

//

//

//

//

//

//
//--

{
    UINT32 Index;

    Index = 0;

    while (String[Index] != 0) {

        Index += 1;
    }

    return Index;
}

UINT32
BlRtlStringLengthW(
    PCWSTR String
    )


//

//

//

//

//

//

//
//--

{
    UINT32 Index;

    Index = 0;

    while (String[Index] != 0) {

        Index += 1;
    }

    return Index;
}

BOOLEAN
BlRtlFormatStringToken(
    PCHAR Output,
    UINT32 OutputSize,
    PCSTR String,
    INT32 Width,
    PUINT32 CharactersConsumed
    )


//

//

//

//

//

//

//

//

//
//

//


//
//--

{
    UINT32 Index;
    UINT32 MinimumWidth;
    UINT32 PadWidth;
    UINT32 StringIndex;
    UINT32 StringLength;

    //
    
    //

    StringLength = BlRtlStringLength(String);

    MinimumWidth = ABS(Width);

    PadWidth = 0;

    if (MinimumWidth > StringLength) {

        PadWidth = MinimumWidth - StringLength;
    }

    //
    
    //

    if ((StringLength + PadWidth) > OutputSize) {

        return FALSE;
    }

    Index = 0;

    //
    
    //

    if (Width > 0) {

        while (PadWidth > 0) {

            Output[Index] = ' ';
            Index += 1;
            PadWidth -= 1;
        }
    }

    //
    
    //

    for (StringIndex = 0; StringIndex < StringLength; StringIndex += 1) {

        Output[Index] = String[StringIndex];
        Index += 1;
    }

    //
    
    //

    while (PadWidth > 0) {

        Output[Index] = ' ';
        Index += 1;
        PadWidth -= 1;
    }

    //
    
    //

    *CharactersConsumed = Index;

    return TRUE;
}

BOOLEAN
BlRtlFormatChar(
    PCHAR Output,
    UINT32 OutputSize,
    CHAR Value,
    PUINT32 CharactersConsumed
    )


//

//

//

//

//

//

//

//
//

//


//
//--

{
    //
    
    //

    if (1 > OutputSize) {

        return FALSE;
    }

    Output[0] = Value;

    //
    
    //

    *CharactersConsumed = 1;

    return TRUE;
}

BOOLEAN
BlRtlFormatString(
    PCHAR Output,
    UINT32 OutputSize,
    PCSTR Format,
    va_list ArgumentList
    )


//

//

//

//

//

//

//

//

//


//
//--

{
    UINT32 CharactersConsumed;
    UINT32 InputIndex;
    UINT32 OutputIndex;
    CHAR PadCharacter;
    UINT8 TokenType;
    INT32 Width;

    InputIndex = 0;
    OutputIndex = 0;

    for (;;) {

        if (OutputIndex == OutputSize) {

            return FALSE;
        }

        if (Format[InputIndex] == 0) {

            Output[OutputIndex] = 0;
            return TRUE;
        }

        if (Format[InputIndex] == '\\') {

            switch (Format[InputIndex + 1]) {

                case '\\': {

                    Output[OutputIndex] = '\\';
                    OutputIndex += 1;
                    break;
                }

                case 'r': {

                    Output[OutputIndex] = '\r';
                    OutputIndex += 1;
                    break;
                }

                case 'n': {

                    Output[OutputIndex] = '\r';
                    OutputIndex += 1;
                    break;
                }

                default: {

                    return FALSE;
                }
            }

            InputIndex += 2;
            continue;
        }

        if (BlRtlParseTypeSpecifier(&Format[InputIndex],
                                    &Width,
                                    &PadCharacter,
                                    &TokenType,
                                    &CharactersConsumed) != FALSE) {

            InputIndex += CharactersConsumed;

            switch (TokenType) {

                case STRING_TOKEN_LONG: {

                    if (BlRtlFormatSignedDecimalLong(&Output[OutputIndex],
                                                     OutputSize - OutputIndex,
                                                     va_arg(ArgumentList, INT32),
                                                     Width,
                                                     &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_ULONG: {

                    if (BlRtlFormatUnsignedLong(&Output[OutputIndex],
                                                OutputSize - OutputIndex,
                                                va_arg(ArgumentList, UINT32),
                                                PadCharacter,
                                                Width,
                                                10,
                                                &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_ULONG_HEX: {

                    if (BlRtlFormatUnsignedLong(&Output[OutputIndex],
                                                OutputSize - OutputIndex,
                                                va_arg(ArgumentList, UINT32),
                                                PadCharacter,
                                                Width,
                                                16,
                                                &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_ULONGLONG: {

                    if (BlRtlFormatUnsignedLongLong(&Output[OutputIndex],
                                                    OutputSize - OutputIndex,
                                                    va_arg(ArgumentList, UINT64),
                                                    PadCharacter,
                                                    Width,
                                                    10,
                                                    &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_ULONGLONG_HEX: {

                    if (BlRtlFormatUnsignedLongLong(&Output[OutputIndex],
                                                    OutputSize - OutputIndex,
                                                    va_arg(ArgumentList, UINT64),
                                                    PadCharacter,
                                                    Width,
                                                    16,
                                                    &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_PVOID: {

#if defined(BOOT_X86)

                    if (BlRtlFormatUnsignedLong(&Output[OutputIndex],
                                                OutputSize - OutputIndex,
                                                va_arg(ArgumentList, UINT32),
                                                '0',
                                                8,
                                                16,
                                                &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

#elif defined(BOOT_X64)

                    if (BlRtlFormatUnsignedLongLong(&Output[OutputIndex],
                                                    OutputSize - OutputIndex,
                                                    va_arg(ArgumentList, UINT64),
                                                    '0',
                                                    16,
                                                    16,
                                                    &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

#endif

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_PCHAR: {

                    if (BlRtlFormatStringToken(&Output[OutputIndex],
                                               OutputSize - OutputIndex,
                                               va_arg(ArgumentList, PCHAR),
                                               Width,
                                               &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }

                case STRING_TOKEN_CHAR: {

                    if (BlRtlFormatChar(&Output[OutputIndex],
                                        OutputSize - OutputIndex,
                                        va_arg(ArgumentList, CHAR),
                                        &CharactersConsumed) == FALSE) {

                        return FALSE;
                    }

                    OutputIndex += CharactersConsumed;
                    break;
                }
            }

            continue;
        }

        Output[OutputIndex] = Format[InputIndex];
        InputIndex += 1;
        OutputIndex += 1;
    }
}

BOOLEAN
BlRtlPrintf(
    PCSTR Format,
    ...
    )


//

//

//

//

//

//

//


//
//--

{
    va_list ArgumentList;
    CHAR Buffer[4096];

    va_start(ArgumentList, Format);

    if (BlRtlFormatString(Buffer, sizeof(Buffer), Format, ArgumentList) == FALSE) {

        return FALSE;
    }

    BlVideoPrintString(Buffer);

    BlKdPrintString(Buffer);

    return TRUE;
}

BOOLEAN
BlRtlEqualStringN(
    PCSTR String1,
    PCSTR String2,
    UINT32 Count
    )


//

//

//

//

//

//

//

//


//
//--

{
    while (Count > 0) {

        if ((*String1 == 0) || (*String2 == 0)) {

            return FALSE;
        }

        if (*String1 != *String2) {

            return FALSE;
        }

        String1 += 1;
        String2 += 1;
        Count -= 1;
    }

    return TRUE;
}

BOOLEAN
BlRtlEqualStringI(
    PCSTR String1,
    PCSTR String2
    )


//

//

//

//

//

//

//


//
//--

{
    for (;;) {

        if (BlRtlConvertCharacterToUpperCase(*String1) != BlRtlConvertCharacterToUpperCase(*String2)) {

            return FALSE;
        }

        if (*String1 == 0) {

            return TRUE;
        }

        String1 += 1;
        String2 += 1;
    }
}

PCSTR
BlRtlFindSubstring(
    PCSTR String,
    PCSTR Substring
    )


//

//

//

//

//

//

//


//
//--

{
    UINT32 SubstringLength;

    SubstringLength = BlRtlStringLength(Substring);

    while (*String != 0) {

        if (BlRtlEqualStringN(String, Substring, SubstringLength) != FALSE) {

            return String;
        }

        String += 1;
    }

    return NULL;
}


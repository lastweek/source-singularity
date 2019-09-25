// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//////////////////////////////////////////////////////////////////////////////
//
// Completely side-effect free string formating .
//

#ifndef _VA_LIST_DEFINED
typedef char *va_list;
#define _VA_LIST_DEFINED

#if !USE_64
#define _INTSIZEOF(n)    ( (sizeof(n) + sizeof(int) - 1) & ~(sizeof(int) - 1) )
#define va_start(ap,v) ap = (va_list)&v + _INTSIZEOF(v)
#define va_arg(ap,t) ( *(t *)((ap += _INTSIZEOF(t)) - _INTSIZEOF(t)) )
#define va_end(ap) ap = (va_list)0

#else  // USE_64

// the following extern "C" code is needed to ensure the
// compiler intrinsic IV_VA_START is invoked.
extern "C" extern void __cdecl __va_start(va_list *, ...);

#define va_dcl          va_list va_alist;
#define va_start(ap,x)   ( __va_start(&ap, x) )
#define va_arg(ap, t)   \
    ( ( sizeof(t) > sizeof(__int64) || ( sizeof(t) & (sizeof(t) - 1) ) != 0 ) \
        ? **(t **)( ( ap += sizeof(__int64) ) - sizeof(__int64) ) \
        :  *(t  *)( ( ap += sizeof(__int64) ) - sizeof(__int64) ) )
#define va_end(ap)      ( ap = (va_list)0 )
#endif  // USE_64

#endif  // _VA_LIST_DEFINED

//
// define a macro to compute the size of a type, variable or expression,
// rounded up to the nearest multiple of sizeof(int). This number is its
// size as function argument (Intel architecture). Note that the macro
// depends on sizeof(int) being a power of 2!
//


#pragma optimize ("", off)

static char *do_base(char * pszOut, ULARGEST nValue, UINT nBase, CHAR xtra)
{
    char szTmp[96];
    int nDigit = sizeof(szTmp)-2;
    for (; nDigit >= 0; nDigit--) {
        UINT n = (UINT)(nValue % nBase);
        szTmp[nDigit] = ((n < 10) ? '0' : (xtra - 10)) + n;
        nValue /= nBase;
    }
    for (nDigit = 0; nDigit < sizeof(szTmp) - 2 && szTmp[nDigit] == '0'; nDigit++) {
        // skip leading zeros.
    }
    for (; nDigit < sizeof(szTmp) - 1; nDigit++) {
        *pszOut++ = szTmp[nDigit];
    }
    *pszOut = '\0';
    return pszOut;
}

#pragma optimize ("", on)

static char * do_str(char * pszOut, char * pszIn)
{
    while (*pszIn) {
        *pszOut++ = *pszIn++;
    }
    *pszOut = '\0';
    return pszOut;
}

static char * do_wstr(char * pszOut, short * pszIn)
{
    while (*pszIn) {
        *pszOut++ = (char)*pszIn++;
    }
    *pszOut = '\0';
    return pszOut;
}

static int do_out(void (*pfOutput)(void *pContext, char c), void *pContext, char *pszIn)
{
    int nOut = 0;

    while (*pszIn) {
        pfOutput(pContext, *pszIn++);
        nOut++;
    }
    return nOut;
}

int strformat(void (*pfOutput)(void *pContext, char c), void *pContext,
              const char * pszFmt, va_list args)
{
    int nOut = 0;

    while (*pszFmt) {
        if (*pszFmt == '%') {
            char szTemp[128];
            char szHead[4] = "";
            int nLen;
            int nWidth = 0;
            int nPrecision = 0;
            int fLeft = 0;
            int fPositive = 0;
            int fPound = 0;
            int fBlank = 0;
            int fZero = 0;
            int fDigit = 0;
            int fSmall = 0;
            int fLarge = 0;
            int fString = 0;
            const char * pszArg = pszFmt;

            pszFmt++;

            for (; (*pszFmt == '-' ||
                    *pszFmt == '+' ||
                    *pszFmt == '#' ||
                    *pszFmt == ' ' ||
                    *pszFmt == '0'); pszFmt++) {
                switch (*pszFmt) {
                  case '-': fLeft = 1; break;
                  case '+': fPositive = 1; break;
                  case '#': fPound = 1; break;
                  case ' ': fBlank = 1; break;
                  case '0': fZero = 1; break;
                }
            }

            if (*pszFmt == '*') {
                nWidth = va_arg(args, int);
                pszFmt++;
            }
            else {
                while (*pszFmt >= '0' && *pszFmt <= '9') {
                    nWidth = nWidth * 10 + (*pszFmt++ - '0');
                }
            }
            if (*pszFmt == '.') {
                pszFmt++;
                fDigit = 1;
                if (*pszFmt == '*') {
                    nPrecision = va_arg(args, int);
                    pszFmt++;
                }
                else {
                    while (*pszFmt >= '0' && *pszFmt <= '9') {
                        nPrecision = nPrecision * 10 + (*pszFmt++ - '0');
                    }
                }
            }

            if (*pszFmt == 'h') {
                fSmall = 1;
                pszFmt++;
            }
            else if (*pszFmt == 'l' || *pszFmt == 'L') {
                fLarge = 1;
                pszFmt++;
            }

            if (*pszFmt == 's' || *pszFmt == 'S' ||
                *pszFmt == 'c' || *pszFmt == 'C') {
                if (*pszFmt == 's' || *pszFmt == 'S') {
                    char * pszDst = szTemp;
                    void * pvData = va_arg(args, void *);

                    if (*pszFmt == 'S') {
                        fLarge = 1;
                    }
                    pszFmt++;

                    fString = 1;
                    if (fSmall) {
                        fLarge = 0;
                    }

                    if (!pvData) {
                        pszDst = do_str(pszDst, "<NULL>");
                    }
                    else if (fLarge) {
                        pszDst = do_wstr(pszDst, (short *)pvData);
                    }
                    else {
                        pszDst = do_str(pszDst, (char *)pvData);
                    }
                    nLen = (int) (pszDst - szTemp);
                }
                else if (*pszFmt == 'c' || *pszFmt == 'C') {
                    if (*pszFmt == 'S') {
                        fLarge = 1;
                    }
                    pszFmt++;

                    fString = 1;

                    szTemp[0] = (char)va_arg(args, int);
                    szTemp[1] = '\0';
                    nLen = 1;
                }

                if (nPrecision && nLen > nPrecision) {
                    nLen = nPrecision;
                    szTemp[nLen] = '\0';
                }

                if (fLeft) {
                    nOut += do_out(pfOutput, pContext, szTemp);
                    for (; nLen < nWidth; nLen++) {
                        pfOutput(pContext, ' ');
                        nOut++;
                    }
                }
                else {
                    for (; nLen < nWidth; nLen++) {
                        pfOutput(pContext, ' ');
                        nOut++;
                    }
                    nOut = do_out(pfOutput, pContext, szTemp);
                }
            }
            else if (*pszFmt == 'p' || *pszFmt == 'u' ||
                     *pszFmt == 'd' || *pszFmt == 'i' || *pszFmt == 'o' ||
                     *pszFmt == 'x' || *pszFmt == 'X' || *pszFmt == 'b') {

                ULARGEST value;
                if (fLarge) {
                    value = va_arg(args, ULARGEST);
                }
                else {
                    value = va_arg(args, unsigned int);
                }

                if (*pszFmt == 'p') {
                    if (nWidth == 0) {
                        nWidth = fLarge ? 2 * sizeof(ULARGEST) : 2 * sizeof(unsigned int);
                        fZero = 1;
                    }
                    pszFmt++;
                    nLen = (int) (do_base(szTemp, value, 16, 'a') - szTemp);
                    if (fPound && value) {
                        do_str(szHead, "0x");
                    }
                }
                else if (*pszFmt == 'x' || *pszFmt == 'p') {
                    pszFmt++;
                    nLen = (int) (do_base(szTemp, value, 16, 'a') - szTemp);
                    if (fPound && value) {
                        do_str(szHead, "0x");
                    }
                }
                else if (*pszFmt == 'X') {
                    pszFmt++;
                    nLen = (int) (do_base(szTemp, value, 16, 'A') - szTemp);
                    if (fPound && value) {
                        do_str(szHead, "0X");
                    }
                }
                else if (*pszFmt == 'd') {
                    pszFmt++;
                    if ((LARGEST)value < 0) {
                        value = -(LARGEST)value;
                        do_str(szHead, "-");
                    }
                    else if (fPositive) {
                        if (value > 0) {
                            do_str(szHead, "+");
                        }
                    }
                    else if (fBlank) {
                        if (value > 0) {
                            do_str(szHead, " ");
                        }
                    }
                    nLen = (int) (do_base(szTemp, value, 10, 'a') - szTemp);
                    nPrecision = 0;
                }
                else if (*pszFmt == 'u') {
                    pszFmt++;
                    nLen = (int) (do_base(szTemp, value, 10, 'a') - szTemp);
                    nPrecision = 0;
                }
                else if (*pszFmt == 'o') {
                    pszFmt++;
                    nLen = (int) (do_base(szTemp, value, 8, 'a') - szTemp);
                    nPrecision = 0;

                    if (fPound && value) {
                        do_str(szHead, "0");
                    }
                }
                else if (*pszFmt == 'b') {
                    pszFmt++;
                    nLen = (int) (do_base(szTemp, value, 2, 'a') - szTemp);
                    nPrecision = 0;

                    if (fPound && value) {
                        do_str(szHead, "0b");
                    }
                }

                int nHead = 0;
                for (; szHead[nHead]; nHead++) {
                    // Count characters in head string.
                }

                if (fLeft) {
                    if (nHead) {
                        nOut += do_out(pfOutput, pContext, szHead);
                        nLen += nHead;
                    }
                    nOut += do_out(pfOutput, pContext, szTemp);
                    for (; nLen < nWidth; nLen++) {
                        pfOutput(pContext, ' ');
                        nOut++;
                    }
                }
                else if (fZero) {
                    if (nHead) {
                        nOut += do_out(pfOutput, pContext, szHead);
                        nLen += nHead;
                    }
                    for (; nLen < nWidth; nLen++) {
                        pfOutput(pContext, '0');
                        nOut++;
                    }
                    nOut += do_out(pfOutput, pContext, szTemp);
                }
                else {
                    if (nHead) {
                        nLen += nHead;
                    }
                    for (; nLen < nWidth; nLen++) {
                        pfOutput(pContext, ' ');
                        nOut++;
                    }
                    if (nHead) {
                        nOut += do_out(pfOutput, pContext, szHead);
                    }
                    nOut += do_out(pfOutput, pContext, szTemp);
                }
            }
            else {
                pszFmt++;
                while (pszArg < pszFmt) {
                    pfOutput(pContext, *pszArg++);
                    nOut++;
                }
            }
        }
        else {
            pfOutput(pContext, *pszFmt++);
            nOut++;
        }
    }
    return nOut;
}

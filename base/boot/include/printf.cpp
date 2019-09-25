// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

////////////////////////////////////////////////// Publicly Visible Interface.
//

void __cdecl PutChar(char cOut);

static void printfout(void * /* pContext */, char c)
{
    PutChar(c);
}

int printf(const char *pszFmt, ...)
{
    int nOut;
    va_list args;

    va_start(args, pszFmt);
    nOut = strformat(printfout, 0, pszFmt, args);
    va_end(args);

    return nOut;
}

int vprintf(const char *pszFmt, va_list args)
{
    int nOut;

    nOut = strformat(printfout, 0, pszFmt, args);

    return nOut;
}

static void sprintfout(void *pContext, char c)
{
    char **ppszOut = (char **)pContext;

    *(*ppszOut)++ = c;
}

int sprintf(char *pszOut, const char *pszFmt, ...)
{
    int nOut;
    va_list args;

    va_start(args, pszFmt);
    nOut = strformat(sprintfout, &pszOut, pszFmt, args);
    va_end(args);

    *pszOut = '\0';

    return nOut;
}

int svprintf(char *pszOut, const char *pszFmt, va_list args)
{
    int nOut;

    nOut = strformat(sprintfout, &pszOut, pszFmt, args);
    *pszOut = '\0';

    return nOut;
}

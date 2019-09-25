// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

#define __T(x)      L ## x
#define _T(x)       __T(x)

wchar_t _LinkDate[] = _T(__DATE__) _T(" ") _T(__TIME__);

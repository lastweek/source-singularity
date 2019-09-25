// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*=============================================================================
**
** Class: Exception
**
** Purpose: The base class for all exceptional conditions.
**
=============================================================================*/

namespace System
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using System.Diagnostics;
    using System.Text;
    using System.Reflection;
#if SINGULARITY_KERNEL
    using Microsoft.Singularity;
#elif SINGULARITY_PROCESS
    using Microsoft.Singularity.V1.Services;
#endif // SINGULARITY_PROCESS


    //| <include path='docs/doc[@for="Exception"]/*' />
    [RequiredByBartok]
    public partial class Exception
    {
        //| <include path='docs/doc[@for="Exception.Exception1"]/*' />
        [RequiredByBartok]
        public Exception(String message) {
            _message = message;
#if SINGULARITY_KERNEL
            //DebugStub.Break();
#elif SINGULARITY_PROCESS
            //DebugService.Break();
#endif // SINGULARITY_PROCESS
        }

        // The following functions are for tryall support.
        // This is the function actually called by the internal runtime
        [NoLoggingForUndo]
        [RequiredByBartok]
        private Exception internalCloneForUndo() {
            /* this function is not allowed to throw an exception. */
            try {
                return cloneForUndo();
            }
            catch (Exception ex) {
                return ex;
            }
        }
        
        // Rest of class must provide method:
        //   Exception cloneForUndo();
    }
}

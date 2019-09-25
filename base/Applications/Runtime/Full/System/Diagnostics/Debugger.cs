// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using Microsoft.Singularity;
using System.Runtime.CompilerServices;

namespace System.Diagnostics
{

    /// <summary>
    /// This class provides some of the methods defined by the CLR's version of
    /// the Debugger static class.  This makes writing portable apps easier.
    /// </summary>
    public /*static*/ sealed class Debugger {
        private Debugger() { }

        public static void Break()
        {
            DebugStub.Break();
        }

        public static bool IsAttached
        {
            [NoHeapAllocation]
            get
            {
#if SINGULARITY_KERNEL
                return DebugStub.IsDebuggerPresent();
#elif SINGULARITY_PROCESS
                return true;
#else
#error No environment has been specified.
#endif
            }
        }

    }
}

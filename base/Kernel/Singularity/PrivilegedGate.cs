////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Processor.cs
//
//  Note:
//

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Scheduling;
using Microsoft.Singularity.V1.Threads;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity
{

    [CLSCompliant(false)]
    [AccessedByRuntime("Method called from HAL.cpp")]
    public class PrivilegedGate
    {

        [NoHeapAllocation]
        [AccessedByRuntime("referenced from c++")]
        public static bool DisableInterrupts()
        {
            if ((ProcessPrivileges.GetCurrentPrivileges().AllowedOperations &
                 ProcessPrivileges.Operations.DisableInterrupts) != 0) {

                return Processor.DisableInterrupts();
            }

            //  ISSUE: Assert here until all instances get cleaned up from SIPs
            //  This assertion should be removed / replaced with something that would
            //  flag / halt / break only the bogus SIP, not the entire system

            VTable.Assert(false, "DisableInterrupts called from unprivileged SIP");

            return false;
        }

        [NoHeapAllocation]
        [AccessedByRuntime("referenced from c++")]
        public static void RestoreInterrupts(bool enabled)
        {
            if ((ProcessPrivileges.GetCurrentPrivileges().AllowedOperations &
                 ProcessPrivileges.Operations.DisableInterrupts) != 0) {

                Processor.RestoreInterrupts(enabled);

            } else {

                //  ISSUE: Assert here until all instances get cleaned up from SIPs
                //  This assertion should be removed / replaced with something that would
                //  flag / halt / break only the bogus SIP, not the entire system

                VTable.Assert(false, "RestoreInterrupts called from unprivileged SIP");
            }
        }

        // Use this method for assertions only!
        [NoHeapAllocation]
        [AccessedByRuntime("referenced from c++")]
        public static bool InterruptsDisabled()
        {
            if ((ProcessPrivileges.GetCurrentPrivileges().AllowedOperations &
                 ProcessPrivileges.Operations.DisableInterrupts) != 0) {

                return Processor.InterruptsDisabled();
            }

            //  ISSUE: Assert here until all instances get cleaned up from SIPs
            //  This assertion should be removed / replaced with something that would
            //  flag / halt / break only the bogus SIP, not the entire system

            VTable.Assert(false, "InterruptsDisabled called from unprivileged SIP");

            return false;
        }
    }
}

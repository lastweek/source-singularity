// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Scheduling;

namespace System.Threading
{
    ///
    /// <summary>
    ///     Event class implementing an event with auto reset symantics such event automatically
    ///     reset to non signaled state when single wait is satisfied. 
    /// 
    ///     This class is interrupt aware: interrupts are disabled during the period when the 
    ///     spin lock is held. Code that deals with interrupt handling, for example HAL 
    ///     communication, that could be reentrant during interrupt handling should use
    ///     this class instead of AutoResetEvent
    /// </summary>
    ///
    [NoCCtor]
    [CLSCompliant(false)]
    public sealed class InterruptAwareAutoResetEvent : InterruptAwareWaitHandle
    {
        ///
        /// <summary>
        ///     Constructor
        ///</summary>
        ///
        /// <param name="initialState">Initial state of an event true indciates that event is signaled</param>
        ///
        public InterruptAwareAutoResetEvent(bool initialState)
            : base(initialState ? WaitHandle.SignalState.Signaled :
                                  WaitHandle.SignalState.Unsignaled,
                   WaitHandle.SignalState.Unsignaled, 
                   SpinLock.Types.InterruptAutoResetEvent)
        {
        }

        [NoHeapAllocation]
        public void InterruptAwareSet()
        {
            base.InterruptAwareSignalOne(SignalState.Signaled);
        }
    }
}
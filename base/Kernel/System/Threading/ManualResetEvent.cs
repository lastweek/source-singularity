////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Thread.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Scheduling;

namespace System.Threading
{
    
    ///
    /// <summary>
    ///     Event class implementing an event with manual reset symantics such event has to 
    ///     be manually set to unsignaled state
    /// </summary>
    ///
    [NoCCtor]
    [CLSCompliant(false)]
    public sealed class ManualResetEvent : WaitHandle
    {
        ///
        /// <summary>
        ///     Constructor
        ///</summary>
        ///
        /// <param name="initialState">Initial state of an event true indciates that event is signaled</param>
        ///
        public ManualResetEvent(bool initialState)
            : base(initialState ? WaitHandle.SignalState.Signaled : 
                                WaitHandle.SignalState.Unsignaled,
                   WaitHandle.SignalState.Signaled,
                   SpinLock.Types.ManualResetEvent)
        {
        }

        ///
        /// <summary>
        ///     Reset an event state to non signaled
        ///</summary>
        ///
        [NoHeapAllocation]
        public bool Reset()
        {
           // Make sure that we don't have any waiters and then change event state to unsignaled
           // in all cases
           SignalAll (WaitHandle.SignalState.Unsignaled, WaitHandle.SignalState.Unsignaled);

           return true;
        }

        ///
        /// <summary>
        ///     Wake up all waiters and leave state signaled, if no waiters present set event into signaled state
        ///</summary>
        ///
        [NoHeapAllocation]
        public bool Set()
        {
            SignalAll (WaitHandle.SignalState.Signaled,WaitHandle.SignalState.Signaled);
            return true;
        }
    }
}

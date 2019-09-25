////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   AutoResetEvent.cs
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
    ///     Event class implementing an event with auto reset symantics such event automatically
    ///     reset to non signaled state when single wait is satisfied
    /// </summary>
    ///
    [NoCCtor]
    [CLSCompliant(false)]
    public sealed class AutoResetEvent : WaitHandle
    {
        ///
        /// <summary>
        ///     Constructor
        ///</summary>
        ///
        /// <param name="initialState">Initial state of an event true indciates that event is signaled</param>
        ///
        public AutoResetEvent(bool initialState)
            : base(initialState ? WaitHandle.SignalState.Signaled : 
                                 WaitHandle.SignalState.Unsignaled,
                   WaitHandle.SignalState.Unsignaled,
                   SpinLock.Types.AutoResetEvent)
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
           // in all the cases
           SignalAll (WaitHandle.SignalState.Unsignaled, WaitHandle.SignalState.Unsignaled);

            return true;
        }

        ///
        /// <summary>
        ///     Wake up one waiter, if no waiters present set event into signaled state
        ///</summary>
        ///
        [NoHeapAllocation]
        public bool Set()
        {
            // Signal one waiter if present otherwise set event to signaled
            SignalOne(WaitHandle.SignalState.Signaled);

            return true;
        }

        ///
        /// <summary>
        ///     Wake up all waiters and if event is not signaled set it into signaled state
        ///</summary>
        ///
        public bool SetAll()
        {
            SignalAll (WaitHandle.SignalState.Signaled,WaitHandle.SignalState.Unsignaled);
            
            return true;
        }
    }
}

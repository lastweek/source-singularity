//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace System.Threading
{

    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    using Microsoft.Bartok.Runtime;

    /// <summary>
    /// A monitor is used for synchronization. Only a single thread can
    /// hold the monitor at any given time.
    /// </summary>

    // Because Monitors are encoded in the MultiUseWord payload, 
    // they must be 8-byte aligned
    [StructAlign(8)]
    [NoCCtor]
    public sealed partial class Monitor {
        /// <summary>
        /// Attempt to enter the monitor, blocking until it is held.
        /// </summary>
        [Intrinsic]
        public static extern void Enter(Object obj);

        [RequiredByBartok("Enter gets lowered to this")]
        private static void EnterImpl(Object obj) {
            Monitor monitor = GetMonitorFromObject(obj);
            monitor.Enter();
        }

        /// <summary>
        /// Exit the monitor.
        /// </summary>
        [Intrinsic]
        public static extern void Exit(Object obj);

        [RequiredByBartok("Exit gets lowered to this")]
        public static void ExitImpl(Object obj) {
            Monitor monitor = GetMonitorFromObject(obj);
            monitor.Exit();
        }
    }
}

// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: ThreadState
//
// Purpose: Enum to represent the different thread states
//
//=============================================================================  

#if ISA_ARM
using System.Runtime.CompilerServices;
#endif

namespace System.Threading
{

     ///
     /// <summary>
     ///    Scheduler thread state
     /// </summary>
     ///
#if ISA_ARM
    [AccessedByRuntime("Referenced in interlocked.cpp")]
#endif
     public enum ThreadState:byte
     {
        Undefined   = 0x0,
        Running     = 0x1,
        Unstarted   = 0x2,
        Stopped     = 0x4,
        Suspended   = 0x8,
        Blocked     = 0x10,
        Runnable    = 0x20,
     }

     ///
     /// <summary>
     ///    Scheduler thread's actions
     /// </summary>
     ///
     public enum ThreadActions
     {
        Undefined   = 0x0,
        Run         = 0x1,
        Unstart     = 0x2,
        Stop        = 0x4,
        Suspend     = 0x8,
        Block       = 0x10,
        MakeRunnable    = 0x20,
        Freeze      = 0x40,
        UnFreeze    = 0x80,
        DelayAbort   = 0x100,
        UndoDelayAbort = 0x200
     }
}

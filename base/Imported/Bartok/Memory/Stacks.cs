////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Primitive stack segment manager
//

//#define TEST_STACK_LINKING
//#define DEBUG_STACK_VERBOSE
#define NO_TRACE_STACKS
namespace Microsoft.Singularity.Memory
{

    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;
    using System.GCs;

    [NoCCtor]
    [AccessedByRuntime("referenced from halstack.asm and stacks.cpp")]
    internal partial class Stacks {

        ////////////////////////////////////////////////////////////////////////////////
        // These values are made available to the stack walking code so it can 
        // detect links when walking stacks. Since the LinkStack stubs hijack the 
        // return address of routines they are linking, so links can be identified 
        // by looking for return addresses in the following ranges during the stack walk.

        [AccessedByRuntime("defined in halstack.asm")]
        [ExternalStaticData]
        internal static byte LinkStackFunctionsBegin;
        [AccessedByRuntime("defined in halstack.asm")]
        [ExternalStaticData]
        internal static byte LinkStackFunctionsLimit;

        [AccessedByRuntime("defined in halstack.asm")]
        [ExternalStaticData]
        internal static byte LinkStackBegin;
        [AccessedByRuntime("defined in halstack.asm")]
        [ExternalStaticData]
        internal static byte LinkStackLimit;

        [AccessedByRuntime("defined in halstack.asm")]
        [ExternalStaticData]
        internal static byte UnlinkStackBegin;
        [AccessedByRuntime("defined in halstack.asm")]
        [ExternalStaticData]
        internal static byte UnlinkStackLimit;

        [AccessedByRuntime("defined in halstack.asm")]
        [ExternalStaticData]
        internal static byte LinkStackStubsBegin;
        [AccessedByRuntime("defined in halstack.asm")]
        [ExternalStaticData]
        internal static byte LinkStackStubsLimit;

        //////////////////////////////////////////////////// LinkStackN Stubs.
        //
        // Note: As per the description in SDN20, the LinkStackN stubs use
        //       a non-standard calling convention.  However, they are
        //       provided here to given Bartok a symbol to reference.
        //

#if PTR_SIZE_32
        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack0(); // Copy 0 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack4(); // Copy 4 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack8(); // Copy 8 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack12(); // Copy 12 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack16(); // Copy 16 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack20(); // Copy 20 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack24(); // Copy 24 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack28(); // Copy 28 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack32(); // Copy 32 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack36(); // Copy 36 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack40(); // Copy 40 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack44(); // Copy 44 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack48(); // Copy 48 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack52(); // Copy 52 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack56(); // Copy 56 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack60(); // Copy 60 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack64(); // Copy 64 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack68(); // Copy 68 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack72(); // Copy 72 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack76(); // Copy 76 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack80(); // Copy 80 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack84(); // Copy 84 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack88(); // Copy 88 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack92(); // Copy 92 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack96(); // Copy 96 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack100(); // Copy 100 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack104(); // Copy 104 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack108(); // Copy 108 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack112(); // Copy 112 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack116(); // Copy 116 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack120(); // Copy 120 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack124(); // Copy 124 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack128(); // Copy 128 bytes of arguments on stack.

#else   // 64-bit case
        // 8-byte pushes only up to 128 bytes (16 args)
        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack0(); // Copy 0 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack8(); // Copy 8 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack16(); // Copy 16 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack24(); // Copy 24 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack32(); // Copy 32 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack40(); // Copy 40 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack48(); // Copy 48 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack56(); // Copy 56 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack64(); // Copy 64 bytes of arguments on stack.

        [StackBound(72)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack72(); // Copy 64 bytes of arguments on stack.

        [StackBound(80)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack80(); // Copy 64 bytes of arguments on stack.

        [StackBound(88)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack88(); // Copy 64 bytes of arguments on stack.

        [StackBound(96)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack96(); // Copy 64 bytes of arguments on stack.

        [StackBound(104)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack104(); // Copy 64 bytes of arguments on stack.

        [StackBound(112)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack112(); // Copy 64 bytes of arguments on stack.

        [StackBound(120)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack120(); // Copy 64 bytes of arguments on stack.

        [StackBound(128)]
        [NoStackLinkCheck]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void LinkStack128(); // Copy 64 bytes of arguments on stack.

#endif

        ////////////////////////////////////////////////// UnlinkStackN Stubs.
        //
        // Note: As per the description in SDN20, the UnlinkStackN stubs use
        //       a non-standard calling convention and should be referenced
        //       only by the LinkStackN stubs which insert them into the stack.
        //       However, they are provided here for completeness.
        //

#if PTR_SIZE_64
        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack0(); // Remove 0 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack8(); // Remove 8 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack16(); // Remove 16 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack24(); // Remove 24 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack32(); // Remove 32 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack40(); // Remove 40 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack48(); // Remove 48 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack56(); // Remove 56 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack64(); // Remove 64 bytes of arguments on stack.

        [StackBound(72)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack72(); // Copy 64 bytes of arguments on stack.

        [StackBound(80)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack80(); // Copy 64 bytes of arguments on stack.

        [StackBound(88)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack88(); // Copy 64 bytes of arguments on stack.


        [StackBound(96)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack96(); // Copy 64 bytes of arguments on stack.

        [StackBound(104)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack104(); // Copy 64 bytes of arguments on stack.

        [StackBound(112)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack112(); // Copy 64 bytes of arguments on stack.

        [StackBound(120)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack120(); // Copy 64 bytes of arguments on stack.

        [StackBound(128)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack128(); // Copy 64 bytes of arguments on stack.

#else
        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack0(); // Remove 0 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack4(); // Remove 4 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack8(); // Remove 8 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack12(); // Remove 12 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack16(); // Remove 16 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack20(); // Remove 20 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack24(); // Remove 24 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack28(); // Remove 28 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack32(); // Remove 32 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack36(); // Remove 36 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack40(); // Remove 40 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack44(); // Remove 44 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack48(); // Remove 48 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack52(); // Remove 52 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack56(); // Remove 56 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack60(); // Remove 60 bytes of arguments on stack.

        [StackBound(64)]
        [NoStackLinkCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("defined in halstack.asm")]
        internal static extern void UnlinkStack64(); // Remove 64 bytes of arguments on stack.

#endif

    }
}

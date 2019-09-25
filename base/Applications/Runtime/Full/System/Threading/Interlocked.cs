// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Threading
{

    using System;
    using System.Runtime.CompilerServices;

#if SINGULARITY_KERNEL
    using Microsoft.Singularity.Memory;
#endif
#if ISA_ARM
    using Microsoft.Singularity;
    using Microsoft.Singularity.Isal;
#endif

    //| <include path='docs/doc[@for="Interlocked"]/*' />
#if ISA_ARM
    [AccessedByRuntime("Routines defined in interlocked.cpp")]
#endif
    public sealed class Interlocked
    {
        private Interlocked() {
        }

        //| <include path='docs/doc[@for="Interlocked.Increment"]/*' />
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern int Increment(ref int location);

        //| <include path='docs/doc[@for="Interlocked.Decrement"]/*' />
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern int Decrement(ref int location);

        //| <include path='docs/doc[@for="Interlocked.Increment1"]/*' />
        [NoHeapAllocation]
        public static long Increment(ref long location) {
            long value = location;
            while (CompareExchange(ref location, value + 1, value) != value) {
                value = location;
            }
            return value+1;
        }

        //| <include path='docs/doc[@for="Interlocked.Decrement1"]/*' />
        [NoHeapAllocation]
        public static long Decrement(ref long location) {
            long value = location;
            while (CompareExchange(ref location, value - 1, value) != value) {
                value = location;
            }
            return value-1;
        }

        //| <include path='docs/doc[@for="Interlocked.Increment1"]/*' />
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static ulong Increment(ref ulong location) {
            ulong value = location;
            while (CompareExchange(ref location, value + 1, value) != value) {
                value = location;
            }
            return value+1;
        }

        //| <include path='docs/doc[@for="Interlocked.Decrement1"]/*' />
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static ulong Decrement(ref ulong location) {
            ulong value = location;
            while (CompareExchange(ref location, value - 1, value) != value) {
                value = location;
            }
            return value-1;
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static ulong Add(ref ulong location, ulong value) {
            ulong tmp = location;
            ulong newValue = tmp + value;

            while (CompareExchange(ref location, newValue, tmp) != tmp) {
                tmp = location;
                newValue = tmp + value;
            }
            return newValue;
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static ulong Subtract(ref ulong location, ulong value) {
            ulong tmp = location;
            ulong newValue = tmp - value;

            while (CompareExchange(ref location, newValue, tmp) != tmp) {
                tmp = location;
                newValue = tmp - value;
            }
            return newValue;
        }

        //| <include path='docs/doc[@for="Interlocked.Exchange"]/*' />
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern int Exchange(ref int location1, int value);


        //| <include path='docs/doc[@for="Interlocked.CompareExchange"]/*' />
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern int CompareExchange(ref int location1, int value, int comparand);

        //| <include path='docs/doc[@for="Interlocked.Exchange1"]/*' />
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern float Exchange(ref float location1, float value);


        //| <include path='docs/doc[@for="Interlocked.CompareExchange1"]/*' />
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern float CompareExchange(ref float location1, float value, float comparand);

        // Added for thread initialization.
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern ThreadState CompareExchange(ref ThreadState location1, ThreadState value, ThreadState comparand);


#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern long CompareExchange(ref long location1, long value, long comparand);

        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern ulong CompareExchange(ref ulong location1, ulong value, ulong comparand);

        //| <include path='docs/doc[@for="Interlocked.Exchange2"]/*' />
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern Object Exchange(ref Object location1, Object value);

        //| <include path='docs/doc[@for="Interlocked.CompareExchange2"]/*' />
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern Object CompareExchange(ref Object location1, Object value, Object comparand);

        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern uint Exchange(ref uint location1, uint value);

        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern uint CompareExchange(ref uint location1, uint value, uint comparand);

        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        // [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern UIntPtr Exchange(ref UIntPtr location1, UIntPtr value);

        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        // [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern UIntPtr CompareExchange(ref UIntPtr location1, UIntPtr value, UIntPtr comparand);

        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern unsafe UIntPtr Exchange(UIntPtr * location1, UIntPtr value);

        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern unsafe UIntPtr CompareExchange(UIntPtr * location1, UIntPtr value, UIntPtr comparand);


        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        public static extern unsafe void * CompareExchange(ref void * location1, void * value, void * comparand);

#if SINGULARITY_KERNEL
        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        internal static extern unsafe HandleTable.HandlePage * CompareExchange(
            ref HandleTable.HandlePage * location1,
            HandleTable.HandlePage * value,
            HandleTable.HandlePage * comparand);

        [CLSCompliant(false)]
#if ISA_IX
        [Intrinsic]
#elif ISA_ARM
        [AccessedByRuntime("defined in interlocked.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
#endif
        [NoHeapAllocation]
        internal static extern unsafe HandleTable.HandleEntry * CompareExchange(
            ref HandleTable.HandleEntry * location1,
            HandleTable.HandleEntry * value,
            HandleTable.HandleEntry * comparand);
#endif

    }
}

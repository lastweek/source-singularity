// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    using Microsoft.Bartok.Runtime;

    [NoCCtor]
    [StructLayout(LayoutKind.Auto)]
    public unsafe struct ArgIterator
    {
        private IntPtr * nextArg;
        private int remainingArgs;

        [NoHeapAllocation]
        public ArgIterator(RuntimeArgumentHandle arglist)
        {
            IntPtr* p = (IntPtr *) arglist.Pointer;
            this.remainingArgs = (int) *p;
            this.nextArg = p + 1;
       }

        [NoHeapAllocation]
        public int GetRemainingCount() {
            return remainingArgs;
        }

        public int Length {
            [NoHeapAllocation]
            get { return remainingArgs; }
        }

        [NoHeapAllocation]
        internal RuntimeType GetArg(int arg, out IntPtr value)
        {
            if (arg < 0 || arg >= remainingArgs) {
                value = IntPtr.Zero;
                return null;
            }
#if ISA_IX86
            value = nextArg[arg * 2];
            return Magic.toRuntimeType(Magic.fromAddress((UIntPtr)nextArg[arg * 2 + 1]));
#elif ISA_IX64
            IntPtr * ptr = (IntPtr *) nextArg[arg];
            value = *ptr;
            return Magic.toRuntimeType(Magic.fromAddress((UIntPtr)(*(ptr+1))));
#elif ISA_ARM
            // TODO: Correct implementation
            value = nextArg[arg * 2];
            return Magic.toRuntimeType(Magic.fromAddress((UIntPtr)nextArg[arg * 2 + 1]));
#else
#error Undefined architecture
#endif
        }

        [NoHeapAllocation]
        public Object GetObjectArg(int arg)
        {
            IntPtr pvalue;
            RuntimeType rt = GetArg(arg, out pvalue);

            return (rt != null &&
                    pvalue != IntPtr.Zero &&
                    rt.classVtable.structuralView == StructuralType.Reference)
                ? Magic.fromAddress(*(UIntPtr *)pvalue)
                : null;
        }

        [NoHeapAllocation]
        internal RuntimeType PopNextArg(out IntPtr value)
        {
            if (remainingArgs == 0) {
                value = IntPtr.Zero;
                return null;
            }
            else {
                RuntimeType type;
#if ISA_IX86
                value = *nextArg++;
                type = Magic.toRuntimeType(Magic.fromAddress((UIntPtr)(*nextArg++)));
#elif ISA_IX64
                IntPtr * ptr = (IntPtr *) *nextArg++;
                value = *ptr;
                type = Magic.toRuntimeType(Magic.fromAddress((UIntPtr)(*(ptr+1))));
#elif ISA_ARM
                // TODO: Correct implementation
                value = *nextArg++;
                type = Magic.toRuntimeType(Magic.fromAddress((UIntPtr)(*nextArg++)));
#else
#error Undefined architecture
#endif

                remainingArgs--;

                return type;
            }
        }

        [CLSCompliant(false)]
        public TypedReference GetNextArg()
        {
            if (remainingArgs == 0) {
                throw new InvalidOperationException
                    ("GetNextArg: No more arguments");
            }

#if ISA_IX86
            IntPtr value = *nextArg++;
            RuntimeType type = Magic.toRuntimeType(
                Magic.fromAddress((UIntPtr)(*nextArg++)));
#elif ISA_IX64
            IntPtr * ptr = (IntPtr *) *nextArg++;
            IntPtr value = *ptr;
            RuntimeType type = Magic.toRuntimeType(
                Magic.fromAddress((UIntPtr)(*(ptr+1))));
#elif ISA_ARM
            // TODO: Correct implementation
            IntPtr value = *nextArg++;
            RuntimeType type = Magic.toRuntimeType(
                Magic.fromAddress((UIntPtr)(*nextArg++)));
#else
#error Undefined architecture
#endif
            remainingArgs--;

            return new TypedReference(value, type);
        }

        [CLSCompliant(false)]
        public RuntimeTypeHandle GetNextArgType()
        {
            if (remainingArgs == 0) {
                throw new InvalidOperationException
                    ("GetNextArgType: No more arguments");
            }
#if ISA_IX86
            return new RuntimeTypeHandle(Magic.toRuntimeType(
                                             Magic.fromAddress(
                                                 (UIntPtr)(nextArg[1]))));
#elif ISA_IX64
            IntPtr * ptr = (IntPtr *) *nextArg;
            return new RuntimeTypeHandle(Magic.toRuntimeType(
                                             Magic.fromAddress(
                                                 (UIntPtr)(*(ptr+1)))));
#elif ISA_ARM
            // TODO: Correct implementation
            return new RuntimeTypeHandle(Magic.toRuntimeType(
                                             Magic.fromAddress(
                                                 (UIntPtr)(nextArg[1]))));
#else
#error Undefined architecture
#endif
        }
    }
}

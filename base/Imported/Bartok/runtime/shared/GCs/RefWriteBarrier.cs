//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs
{
    using Microsoft.Bartok.Runtime;
    using System.Runtime.CompilerServices;
    using System.Threading;

    internal abstract unsafe class RefWriteBarrier: Barrier
    {
        [NoBarriers]
        protected override int AtomicSwapImpl(ref int location,
                                              int value,
                                              int mask)
        {
            return Interlocked.Exchange(ref location, value);
        }
        
        [NoBarriers]
        protected override UIntPtr AtomicSwapImpl(ref UIntPtr location,
                                                  UIntPtr value,
                                                  int mask)
        {
            return Interlocked.Exchange(ref location, value);
        }

        [NoBarriers]
        protected override int AtomicCompareAndSwapImpl(ref int location,
                                                        int newValue,
                                                        int comparand,
                                                        int mask)
        {
            return Interlocked.CompareExchange(ref location,
                                               newValue, comparand);
        }

        [NoBarriers]
        protected override long AtomicCompareAndSwapImpl(ref long location,
                                                         long newValue,
                                                         long comparand,
                                                         int mask)
        {
            return Interlocked.CompareExchange(ref location,
                                               newValue, comparand);
        }

        [NoBarriers]
        protected override
        UIntPtr AtomicCompareAndSwapImpl(ref UIntPtr location,
                                         UIntPtr newValue,
                                         UIntPtr comparand,
                                         int mask)
        {
            return Interlocked.CompareExchange(ref location,
                                               newValue, comparand);
        }

        [Inline]
        [NoBarriers]
        protected override Object WeakRefReadImpl(UIntPtr addr, int mask)
        {
            return Magic.fromAddress(addr);
        }

        [Inline]
        [NoBarriers]
        protected override UIntPtr WeakRefWriteImpl(Object obj,
                                                   int mask)
        {
            return Magic.addressOf(obj);
        }
        
        [Inline]
        [NoBarriers]
        protected override bool EqImpl(Object a,Object b, int mask)
        {
            return a==b;
        }
        
        [Inline]
        [NoBarriers]
        protected override bool AllowFastPathImpl() {
            return false;
        }

        [Inline]
        protected override void WriteImpl(float *location,
                                          float value,
                                          int mask)
        {
            *location = value;
        }
        
        [Inline]
        protected override void WriteImpl(double *location,
                                          double value,
                                          int mask)
        {
            *location = value;
        }
        
        [Inline]
        protected override void WriteImpl(byte *location,
                                          byte value,
                                          int mask)
        {
            *location = value;
        }
        
        [Inline]
        protected override void WriteImpl(ushort *location,
                                          ushort value,
                                          int mask)
        {
            *location = value;
        }
        
        [Inline]
        protected override void WriteImpl(uint *location,
                                          uint value,
                                          int mask)
        {
            *location = value;
        }
        
        [Inline]
        protected override void WriteImpl(ulong *location,
                                          ulong value,
                                          int mask)
        {
            *location = value;
        }
        
        [Inline]
        protected override void WriteImpl(UIntPtr *location,
                                          UIntPtr value,
                                          int mask)
        {
            *location = value;
        }

        [Inline]
        protected override Object ReadObjImpl(UIntPtr *location,
                                              int mask)
        {
            return Magic.fromAddress(*location);
        }

        [Inline]
        protected override float ReadImpl(float *location,
                                          int mask)
        {
            return *location;
        }

        [Inline]
        protected override double ReadImpl(double *location,
                                           int mask)
        {
            return *location;
        }

        [Inline]
        protected override byte ReadImpl(byte *location,
                                         int mask)
        {
            return *location;
        }

        [Inline]
        protected override ushort ReadImpl(ushort *location,
                                           int mask)
        {
            return *location;
        }

        [Inline]
        protected override uint ReadImpl(uint *location,
                                         int mask)
        {
            return *location;
        }

        [Inline]
        protected override ulong ReadImpl(ulong *location,
                                          int mask)
        {
            return *location;
        }

        [Inline]
        protected override UIntPtr ReadImpl(UIntPtr *location,
                                            int mask)
        {
            return *location;
        }
        
        [NoBarriers]
        [Inline]
        protected override void WriteImplByRef(ref float location,
                                               float value,
                                               int mask)
        {
            location = value;
        }
        
        [NoBarriers]
        [Inline]
        protected override void WriteImplByRef(ref double location,
                                               double value,
                                               int mask)
        {
            location = value;
        }
        
        [NoBarriers]
        [Inline]
        protected override void WriteImplByRef(ref byte location,
                                               byte value,
                                               int mask)
        {
            location = value;
        }
        
        [NoBarriers]
        [Inline]
        protected override void WriteImplByRef(ref ushort location,
                                               ushort value,
                                               int mask)
        {
            location = value;
        }
        
        [NoBarriers]
        [Inline]
        protected override void WriteImplByRef(ref uint location,
                                               uint value,
                                               int mask)
        {
            location = value;
        }
        
        [NoBarriers]
        [Inline]
        protected override void WriteImplByRef(ref ulong location,
                                               ulong value,
                                               int mask)
        {
            location = value;
        }
        
        [NoBarriers]
        [Inline]
        protected override void WriteImplByRef(ref UIntPtr location,
                                               UIntPtr value,
                                               int mask)
        {
            location = value;
        }

        [NoBarriers]
        [Inline]
        protected override Object ReadImplByRef(ref Object location,
                                                int mask)
        {
            return location;
        }

        [NoBarriers]
        [Inline]
        protected override float ReadImplByRef(ref float location,
                                               int mask)
        {
            return location;
        }
        
        [NoBarriers]
        [Inline]
        protected override double ReadImplByRef(ref double location,
                                                int mask)
        {
            return location;
        }

        [NoBarriers]
        [Inline]
        protected override byte ReadImplByRef(ref byte location,
                                              int mask)
        {
            return location;
        }

        [NoBarriers]
        [Inline]
        protected override ushort ReadImplByRef(ref ushort location,
                                                int mask)
        {
            return location;
        }

        [NoBarriers]
        [Inline]
        protected override uint ReadImplByRef(ref uint location,
                                              int mask)
        {
            return location;
        }

        [NoBarriers]
        [Inline]
        protected override ulong ReadImplByRef(ref ulong location,
                                               int mask)
        {
            return location;
        }

        [NoBarriers]
        [Inline]
        protected override UIntPtr ReadImplByRef(ref UIntPtr location,
                                                 int mask)
        {
            return location;
        }

        [Inline]
        protected override Object LoadStaticFieldImpl(ref Object staticField,
                                                      int mask)
        {
            return this.ReadImplByRef(ref staticField, mask);
        }
    }
}


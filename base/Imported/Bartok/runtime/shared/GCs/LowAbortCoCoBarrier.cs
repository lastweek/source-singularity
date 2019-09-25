//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs {

    using Microsoft.Bartok.Runtime;
    using Microsoft.Bartok.Options;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

    internal unsafe abstract class LowAbortCoCoBarrier: CoCoBarrier {

        // note that this the mixinConditional
        // for CoCo

        [MixinConditional("LowAbortCoCo")]
        [Mixin(typeof(PreHeader))]
        internal struct CoCoPreHeader {
            internal MultiUseWord muw;
            internal UIntPtr CoCoWord;
        }

        [MixinConditional("LowAbortCoCo")]
        [Mixin(typeof(Object))]
        internal class CoCoObject: System.Object {
            internal new CoCoPreHeader preHeader;
        }

        internal static CoCoObject MixinObject(Object o)
        {
            return (CoCoObject)o;
        }

        [NoBarriers]
        internal static new void Initialize()
        {
            CoCoBarrier.Initialize();
        }

        internal override void InitLateStub()
        {
            CoCoWordOffset =
                (UIntPtr)Magic.toPointer(ref MixinObject(interlock).preHeader.CoCoWord)
                - Magic.addressOf(interlock);
        }

        // shifts 1 left by size bytes.  if size is 4, returns 0.
        [Inline]
        internal static int Shlb1(UIntPtr size)
        {
            int halfAmount=(int)(uint)size*4;
            return 1<<halfAmount<<halfAmount;
        }

        // These methods are for writing.  When we write, we always write
        // aligned words.  These methods provide two pieces of functionality:
        // 1) create word masks that tell us which part of a word is being
        //    modified, and
        // 2) the new values of the words being modified (with the bits not
        //    in the corresponding masks having arbitrary values)

        // Creates a mask for the part of a 32-bit word that starts at
        // the lowOffset byte and is size bytes in size.
        [Inline]
        internal static UIntPtr MakeMask(UIntPtr lowOffset,
                                         UIntPtr size)
        {
            return (UIntPtr)(uint)((Shlb1(size)-1)<<(int)(uint)(lowOffset*8));
        }

        // convenience method, same as above.
        [Inline]
        internal static UIntPtr MakeMask(int lowOffset,
                                         UIntPtr size)
        {
            return MakeMask((UIntPtr)(uint)lowOffset, size);
        }

        // moves bytes up by lowOffset bytes, and then returns the
        // first 32 bits.
        [Inline]
        internal static UIntPtr Shift(ulong value,
                                      UIntPtr lowOffset)
        {
            return (UIntPtr)((value<<(int)(uint)(lowOffset*8))&(ulong)UIntPtr.MaxValue);
        }

        // moves bytes down by lowOffset, and then returns the first
        // 32 bits.
        [Inline]
        internal static UIntPtr UnShift(ulong value,
                                        UIntPtr lowOffset)
        {
            return (UIntPtr)((value>>(int)(uint)(lowOffset*8))&(ulong)UIntPtr.MaxValue);
        }

        // These methods are for reading.  When we read, we want to
        // reassemble words into a ulong.  The words and the ulong may not
        // be aligned.  Thus, for each word, we want to be able to
        // mask off the part of the word that belongs to the ulong, and then
        // shift it into position.  It turns out that there are only
        // two cases (covered ShiftMask and UnShiftMask).  It is never
        // necessary to take an arbitrary part of a word and shift it to
        // an arbitrary part of the resulting ulong.

        // Mask off the first size bytes of the word and then shift it up
        // to lowOffset.
        [Inline]
        internal static ulong ShiftMask(UIntPtr value,
                                        UIntPtr lowOffset,
                                        UIntPtr size)
        {
            return ((ulong)(value&(UIntPtr)(uint)(Shlb1(size)-1)))<<(int)(uint)(lowOffset*8);
        }

        // take size bytes above lowOffset and shift them all the way
        // down.
        [Inline]
        internal static ulong UnShiftMask(UIntPtr value,
                                          UIntPtr lowOffset,
                                          UIntPtr size)
        {
            return (ulong)((value>>(int)(uint)(lowOffset*8))&(UIntPtr)(uint)(Shlb1(size)-1));
        }

        [NoBarriers]
        [TrustedNonNull]
        internal static LowAbortCoCoBarrier laInstance;

        internal void InitEarly()
        {
            instance = laInstance = this;
        }

        internal LowAbortCoCoBarrier()
        {
        }

        [NoBarriers]
        internal override bool ObjectIsNotCopied(Object o)
        {
            return MixinObject(o).preHeader.CoCoWord==0;
        }

        [NoInline]
        [CalledRarely]
        internal static UIntPtr PinSlow(UIntPtr address)
        {
            return laInstance.DoPin(address, Pinner.Barrier);
        }

        [Inline]
        protected override UIntPtr PinImpl(UIntPtr address,
                                           int mask)
        {
            if (AllowPinFastPath(mask)) {
                return address;
            } else {
                return PinSlow(address);
            }
        }

        internal static bool EqImpl(UIntPtr a, UIntPtr b, bool isObject)
        {
            return a == b
                || (isObject && forwarding &&
                    ToSpaceBeforeReadyImpl(Magic.fromAddress(a))
                    == ToSpaceBeforeReadyImpl(Magic.fromAddress(b)));
        }

        [NoBarriers]
        [NoInline]
        [CalledRarely]
        internal static bool EqImplSlow(Object a, Object b)
        {
            return ToSpaceBeforeReadyImpl(a) == ToSpaceBeforeReadyImpl(b);
        }

        [NoBarriers]
        [Inline]
        protected override bool EqImpl(Object a, Object b, int mask)
        {
            // why this works: either a==b or not.  if not, then
            // this trivially works.  if a==b, then either the object
            // that a and b refer to is forwarded, is going to be
            // forwarded while this runs, or it isn't forwarded.  if
            // it isn't, a, b, ToSpace(a) and ToSpace(b) will all
            // trivially give the same address.  if it is forwarded
            // right now, then forcing forwarding on both pointers
            // guarantees correctness.  if it will be forwarded as
            // this runs, ToSpace(a) == ToSpace(b) may fail (one may
            // observe forwarding while the other doesn't), but
            // a == b will be correct.
            if ((mask & BarrierMask.PathSpec.UseMask)!=0) {
                if (StrictlyAllowFastPath(mask)) {
                    return a==b;
                } else {
                    return a == b || EqImplSlow(a, b);
                }
            } else {
                return a == b || (forwarding && EqImplSlow(a, b));
            }
        }

        [AssertDevirtualize]
        protected abstract UIntPtr ReadWordSlow(Object o,
                                                UIntPtr offset);

        [NoInline]
        [CalledRarely]
        internal static UIntPtr ReadWordSlow(Object o,
                                             void *ptr)
        {
            UIntPtr offset = (UIntPtr)ptr-Magic.addressOf(o);
            if (fVerbose && DebugThread) {
                VTable.DebugPrint("o = ");
                VTable.DebugPrint((ulong)Magic.addressOf(o));
                VTable.DebugPrint(", ptr = ");
                VTable.DebugPrint((ulong)ptr);
                VTable.DebugPrint(", offset = ");
                VTable.DebugPrint((ulong)offset);
                VTable.DebugPrint("\n");
            }
            return laInstance.ReadWordSlow(o, offset);
        }

        [NoInline]
        [CalledRarely]
        internal static Object ReadObjImplSlow(Object o, UIntPtr *ptr)
        {
            return ToSpaceAsObj(ReadWordSlow(o, ptr));
        }

        [Inline]
        protected override Object ReadObjImpl(Object o,
                                              UIntPtr *ptr,
                                              int mask)
        {
            if (AllowFastPath(mask)) {
                return Magic.fromAddress(*ptr);
            } else {
                return ReadObjImplSlow(o, ptr);
            }
        }

        [Inline]
        internal static ulong LoadSlow(Object o,
                                       UIntPtr offset,
                                       UIntPtr size)
        {
            UIntPtr maxLowOff=(UIntPtr)sizeof(UIntPtr);
            UIntPtr lowMask=maxLowOff-1;
            UIntPtr lowOff=offset&lowMask;
            offset&=~lowMask;
            if (lowOff+size>maxLowOff*2) {
                return UnShiftMask(laInstance.ReadWordSlow(o, offset),
                                   lowOff,
                                   maxLowOff-lowOff)
                    | ShiftMask(laInstance.ReadWordSlow(o, offset+maxLowOff),
                                maxLowOff-lowOff,
                                UIntPtr.MaxValue)
                    | ShiftMask(laInstance.ReadWordSlow(o, offset+maxLowOff*2),
                                maxLowOff*2-lowOff,
                                lowOff+size-maxLowOff);
            } else if (lowOff+size>maxLowOff) {
                return UnShiftMask(laInstance.ReadWordSlow(o, offset),
                                   lowOff,
                                   maxLowOff-lowOff)
                    | ShiftMask(laInstance.ReadWordSlow(o, offset+maxLowOff),
                                maxLowOff-lowOff,
                                lowOff+size-maxLowOff);
            } else {
                return UnShiftMask(laInstance.ReadWordSlow(o, offset),
                                   lowOff,
                                   size);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static ulong LoadSlow(Object o,
                                       UIntPtr offset,
                                       int size)
        {
            return LoadSlow(o, offset, (UIntPtr)size);
        }

        [NoInline]
        [CalledRarely]
        internal static ulong LoadSlow(Object o,
                                       void *ptr,
                                       int size)
        {
            return LoadSlow(o, (UIntPtr)ptr-Magic.addressOf(o), (UIntPtr)size);
        }

        [NoInline]
        [CalledRarely]
        internal static float ReadSlow(Object o,
                                        float *ptr)
        {
            return IntToFloatBits((uint)LoadSlow(o, ptr, 4));
        }

        [Inline]
        protected override float ReadImpl(Object o,
                                          float *ptr,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(o, ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static double ReadSlow(Object o,
                                        double *ptr)
        {
            return LongToDoubleBits(LoadSlow(o, ptr, 8));
        }

        [Inline]
        protected override double ReadImpl(Object o,
                                           double *ptr,
                                           int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(o, ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static byte ReadSlow(Object o,
                                      byte *ptr)
        {
            return (byte)LoadSlow(o, ptr, 1);
        }

        [Inline]
        protected override byte ReadImpl(Object o,
                                         byte *ptr,
                                         int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(o, ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static ushort ReadSlow(Object o,
                                        ushort *ptr)
        {
            return (ushort)LoadSlow(o, ptr, 2);
        }

        [Inline]
        protected override ushort ReadImpl(Object o,
                                           ushort *ptr,
                                           int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(o, ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static uint ReadSlow(Object o,
                                      uint *ptr)
        {
            return (uint)LoadSlow(o, ptr, 4);
        }

        [Inline]
        protected override uint ReadImpl(Object o,
                                         uint *ptr,
                                         int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(o, ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static ulong ReadSlow(Object o,
                                       ulong *ptr)
        {
            return (ulong)LoadSlow(o, ptr, 8);
        }

        [Inline]
        protected override ulong ReadImpl(Object o,
                                          ulong *ptr,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(o, ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static UIntPtr ReadSlow(Object o,
                                         UIntPtr *ptr)
        {
            return (UIntPtr)LoadSlow(o, ptr, sizeof(UIntPtr));
        }

        [Inline]
        protected override UIntPtr ReadImpl(Object o,
                                            UIntPtr *ptr,
                                            int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(o, ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static ulong LoadSlow(void *ptr, int size)
        {
            UIntPtr baseAddr = FindObjectForPreInteriorPtr((UIntPtr)ptr);
            if (baseAddr == UIntPtr.Zero) {
                switch (size) {
                case 1: return (ulong)*(byte*)ptr;
                case 2: return (ulong)*(ushort*)ptr;
                case 4: return (ulong)*(uint*)ptr;
                case 8: return *(ulong*)ptr;
                default: VTable.NotReached(); return 0;
                }
            } else {
                return LoadSlow(Magic.fromAddress(baseAddr), ptr, size);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static Object ReadObjSlow(UIntPtr *ptr)
        {
            return ToSpaceAsObj((UIntPtr)LoadSlow(ptr, sizeof(UIntPtr)));
        }

        [Inline]
        protected override Object ReadObjImpl(UIntPtr *ptr,
                                              int mask)
        {
            if (AllowFastPath(mask)) {
                return Magic.fromAddress(*ptr);
            } else {
                return ReadObjSlow(ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static float ReadSlow(float *ptr)
        {
            return IntToFloatBits((uint)LoadSlow(ptr, 4));
        }

        [Inline]
        protected override float ReadImpl(float *ptr,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static double ReadSlow(double *ptr)
        {
            return LongToDoubleBits((ulong)LoadSlow(ptr, 8));
        }

        [Inline]
        protected override double ReadImpl(double *ptr,
                                           int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static byte ReadSlow(byte *ptr)
        {
            return (byte)LoadSlow(ptr, 1);
        }

        [Inline]
        protected override byte ReadImpl(byte *ptr,
                                         int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static ushort ReadSlow(ushort *ptr)
        {
            return (ushort)LoadSlow(ptr, 2);
        }

        [Inline]
        protected override ushort ReadImpl(ushort *ptr,
                                           int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static uint ReadSlow(uint *ptr)
        {
            return (uint)LoadSlow(ptr, 4);
        }

        [Inline]
        protected override uint ReadImpl(uint *ptr,
                                         int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static ulong ReadSlow(ulong *ptr)
        {
            return (ulong)LoadSlow(ptr, 8);
        }

        [Inline]
        protected override ulong ReadImpl(ulong *ptr,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(ptr);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static UIntPtr ReadSlow(UIntPtr *ptr)
        {
            return (UIntPtr)LoadSlow(ptr, sizeof(UIntPtr));
        }

        [Inline]
        protected override UIntPtr ReadImpl(UIntPtr *ptr,
                                            int mask)
        {
            if (AllowIdleFastPath(mask)) {
                return *ptr;
            } else {
                return ReadSlow(ptr);
            }
        }

        [Inline]
        protected override Object ReadImplByRef(ref Object loc,
                                                int mask)
        {
            return ReadObjImpl(Magic.toPointer(ref loc), mask);
        }

        [Inline]
        protected override float ReadImplByRef(ref float loc,
                                               int mask)
        {
            return ReadImpl((float*)Magic.toPointer(ref loc), mask);
        }

        [Inline]
        protected override double ReadImplByRef(ref double loc,
                                                int mask)
        {
            return ReadImpl((double*)Magic.toPointer(ref loc), mask);
        }

        [Inline]
        protected override byte ReadImplByRef(ref byte loc,
                                              int mask)
        {
            return ReadImpl((byte*)Magic.toPointer(ref loc), mask);
        }

        [Inline]
        protected override ushort ReadImplByRef(ref ushort loc,
                                                int mask)
        {
            return ReadImpl((ushort*)Magic.toPointer(ref loc), mask);
        }

        [Inline]
        protected override uint ReadImplByRef(ref uint loc,
                                              int mask)
        {
            return ReadImpl((uint*)Magic.toPointer(ref loc), mask);
        }

        [Inline]
        protected override ulong ReadImplByRef(ref ulong loc,
                                               int mask)
        {
            return ReadImpl((ulong*)Magic.toPointer(ref loc), mask);
        }

        [Inline]
        protected override UIntPtr ReadImplByRef(ref UIntPtr loc,
                                                 int mask)
        {
            return ReadImpl((UIntPtr*)Magic.toPointer(ref loc), mask);
        }

        // this method is expected to invoke the target barrier
        [AssertDevirtualize]
        protected abstract void WriteWordSlow(Object o,
                                              UIntPtr offset,
                                              UIntPtr mask,
                                              UIntPtr shiftedValue,
                                              bool isObject);

        [NoInline]
        [CalledRarely]
        internal static void WriteWordSlow(Object o,
                                           UIntPtr offset,
                                           UIntPtr mask,
                                           UIntPtr shiftedValue)
        {
            laInstance.WriteWordSlow(o, offset, mask, shiftedValue, false);
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteWordSlowObj(Object o,
                                              UIntPtr *ptr,
                                              UIntPtr value)
        {
            laInstance.WriteWordSlow(o,
                                   (UIntPtr)ptr-Magic.addressOf(o),
                                   UIntPtr.MaxValue,
                                   value,
                                   true);
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteWordSlowObj(Object o,
                                              UIntPtr *ptr,
                                              Object value)
        {
            UIntPtr valueBits=Magic.addressOf(value);
            SourceBarrierWithForward(valueBits);
            WriteWordSlowObj(o, ptr, valueBits);
        }

        [ForceInline]
        protected override void WriteImpl(Object o,
                                          UIntPtr *ptr,
                                          Object value,
                                          int mask)
        {
            if (AllowFastPath(mask)) {
                UIntPtr valueBits=Magic.addressOf(value);
                TargetAndSourceBarrierNoForward(ptr, valueBits);
                *ptr = valueBits;
            } else {
                WriteWordSlowObj(o, ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void StoreSlow(Object o,
                                       void *ptr,
                                       UIntPtr size,
                                       ulong value)
        {
            UIntPtr offset=(UIntPtr)ptr-Magic.addressOf(o);

            if (fVerbose && DebugThread) {
                VTable.DebugPrint("Doing a StoreSlow on ");
                VTable.DebugPrint((ulong)Magic.addressOf(o));
                VTable.DebugPrint(" + ");
                VTable.DebugPrint((ulong)offset);
                VTable.DebugPrint(" the value ");
                VTable.DebugPrint(value);
                VTable.DebugPrint(" of size ");
                VTable.DebugPrint((ulong)size);
                VTable.DebugPrint("\n");
            }

            UIntPtr maxLowOff=(UIntPtr)sizeof(UIntPtr);
            UIntPtr lowMask=maxLowOff-1;
            UIntPtr lowOff=offset&lowMask;
            offset&=~lowMask;
            if (lowOff+size>maxLowOff*2) {
                WriteWordSlow(o,
                              offset,
                              MakeMask(lowOff,
                                       maxLowOff-lowOff),
                              Shift(value,
                                    lowOff));
                WriteWordSlow(o,
                              offset+maxLowOff,
                              UIntPtr.MaxValue,
                              UnShift(value,
                                      maxLowOff-lowOff));
                WriteWordSlow(o,
                              offset+maxLowOff*2,
                              MakeMask(0,
                                       lowOff+size-maxLowOff),
                              UnShift(value,
                                      maxLowOff*2-lowOff));
            } else if (lowOff+size>maxLowOff) {
                WriteWordSlow(o,
                              offset,
                              MakeMask(lowOff,
                                       maxLowOff-lowOff),
                              Shift(value,
                                    lowOff));
                WriteWordSlow(o,
                              offset+maxLowOff,
                              MakeMask(0,
                                       lowOff+size-maxLowOff),
                              UnShift(value,
                                      maxLowOff-lowOff));
            } else {
                WriteWordSlow(o,
                              offset,
                              MakeMask(lowOff,
                                       size),
                              Shift(value,
                                    lowOff));
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void StoreSlow(Object o,
                                       void *ptr,
                                       int size,
                                       ulong value)
        {
            StoreSlow(o, ptr, (UIntPtr)size, value);
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(Object o,
                                       float *ptr,
                                       float value)
        {
            StoreSlow(o, ptr, 4, FloatToIntBits(value));
        }

        [Inline]
        protected override void WriteImpl(Object o,
                                          float *ptr,
                                          float value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr = value;
            } else {
                WriteSlow(o, ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(Object o,
                                       double *ptr,
                                       double value)
        {
            StoreSlow(o, ptr, 8, DoubleToLongBits(value));
        }

        [Inline]
        protected override void WriteImpl(Object o,
                                          double *ptr,
                                          double value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr = value;
            } else {
                WriteSlow(o, ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(Object o,
                                       byte *ptr,
                                       byte value)
        {
            StoreSlow(o, ptr, 1, value);
        }

        [Inline]
        protected override void WriteImpl(Object o,
                                          byte *ptr,
                                          byte value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr = value;
            } else {
                WriteSlow(o, ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(Object o,
                                       ushort *ptr,
                                       ushort value)
        {
            StoreSlow(o, ptr, 2, value);
        }

        [Inline]
        protected override void WriteImpl(Object o,
                                          ushort *ptr,
                                          ushort value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr = value;
            } else {
                WriteSlow(o, ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(Object o,
                                       uint *ptr,
                                       uint value)
        {
            StoreSlow(o, ptr, 4, value);
        }

        [Inline]
        protected override void WriteImpl(Object o,
                                          uint *ptr,
                                          uint value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr = value;
            } else {
                WriteSlow(o, ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(Object o,
                                       ulong *ptr,
                                       ulong value)
        {
            StoreSlow(o, ptr, 8, value);
        }

        [Inline]
        protected override void WriteImpl(Object o,
                                          ulong *ptr,
                                          ulong value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr = value;
            } else {
                WriteSlow(o, ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(Object o,
                                       UIntPtr *ptr,
                                       UIntPtr value)
        {
            StoreSlow(o, ptr, sizeof(UIntPtr), (ulong)value);
        }

        [Inline]
        protected override void WriteImpl(Object o,
                                          UIntPtr *ptr,
                                          UIntPtr value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr = value;
            } else {
                WriteSlow(o, ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteWordSlowObj(UIntPtr *ptr,
                                              Object value)
        {
            UIntPtr valueBits=Magic.addressOf(value);
            SourceBarrierWithForward(valueBits);
            UIntPtr baseAddr = FindObjectForPreInteriorPtr((UIntPtr)ptr);
            if (baseAddr == UIntPtr.Zero) {
                TargetBarrierWithForward(*ptr);
                *ptr=valueBits;
            } else {
                WriteWordSlowObj(Magic.fromAddress(baseAddr),
                                 ptr,
                                 valueBits);
            }
        }

        [ForceInline]
        protected override void WriteImpl(UIntPtr *ptr,
                                          Object value,
                                          int mask)
        {
            if (AllowFastPath(mask)) {
                UIntPtr valueBits=Magic.addressOf(value);
                TargetAndSourceBarrierNoForward(ptr, valueBits);
                *ptr=valueBits;
            } else {
                WriteWordSlowObj(ptr, value);
            }
        }

        internal static void StoreSlow(void *ptr,
                                       int size,
                                       ulong value)
        {
            UIntPtr baseAddr = FindObjectForPreInteriorPtr((UIntPtr)ptr);
            if (baseAddr == UIntPtr.Zero) {
                switch (size) {
                case 1: *(byte*)ptr=(byte)value; break;
                case 2: *(ushort*)ptr=(ushort)value; break;
                case 4: *(uint*)ptr=(uint)value; break;
                case 8: *(ulong*)ptr=value; break;
                default: VTable.NotReached(); break;
                }
            } else {
                StoreSlow(Magic.fromAddress(baseAddr), ptr, size, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(float *ptr,
                                       float value)
        {
            StoreSlow(ptr, 4, FloatToIntBits(value));
        }

        [Inline]
        protected override void WriteImpl(float *ptr,
                                          float value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr=value;
            } else {
                WriteSlow(ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(double *ptr,
                                       double value)
        {
            StoreSlow(ptr, 8, DoubleToLongBits(value));
        }

        [Inline]
        protected override void WriteImpl(double *ptr,
                                          double value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr=value;
            } else {
                WriteSlow(ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(byte *ptr,
                                       byte value)
        {
            StoreSlow(ptr, 1, value);
        }

        [Inline]
        protected override void WriteImpl(byte *ptr,
                                          byte value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr=value;
            } else {
                WriteSlow(ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(ushort *ptr,
                                       ushort value)
        {
            StoreSlow(ptr, 2, value);
        }

        [Inline]
        protected override void WriteImpl(ushort *ptr,
                                          ushort value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr=value;
            } else {
                WriteSlow(ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(uint *ptr,
                                       uint value)
        {
            StoreSlow(ptr, 4, value);
        }

        [Inline]
        protected override void WriteImpl(uint *ptr,
                                          uint value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr=value;
            } else {
                WriteSlow(ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(ulong *ptr,
                                       ulong value)
        {
            StoreSlow(ptr, 8, value);
        }

        [Inline]
        protected override void WriteImpl(ulong *ptr,
                                          ulong value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr=value;
            } else {
                WriteSlow(ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void WriteSlow(UIntPtr *ptr,
                                       UIntPtr value)
        {
            StoreSlow(ptr, sizeof(UIntPtr), (ulong)value);
        }

        [Inline]
        protected override void WriteImpl(UIntPtr *ptr,
                                          UIntPtr value,
                                          int mask)
        {
            if (AllowIdleFastPath(mask)) {
                *ptr=value;
            } else {
                WriteSlow(ptr, value);
            }
        }

        [ForceInline]
        protected override void WriteImplByRef(ref Object loc,
                                               Object value,
                                               int mask)
        {
            WriteImpl(Magic.toPointer(ref loc), value, mask);
        }

        [Inline]
        protected override void WriteImplByRef(ref byte loc,
                                               byte value,
                                               int mask)
        {
            WriteImpl(Magic.toPointer(ref loc), value, mask);
        }

        [Inline]
        protected override void WriteImplByRef(ref ushort loc,
                                               ushort value,
                                               int mask)
        {
            WriteImpl(Magic.toPointer(ref loc), value, mask);
        }

        [Inline]
        protected override void WriteImplByRef(ref uint loc,
                                               uint value,
                                               int mask)
        {
            WriteImpl(Magic.toPointer(ref loc), value, mask);
        }

        [Inline]
        protected override void WriteImplByRef(ref ulong loc,
                                               ulong value,
                                               int mask)
        {
            WriteImpl(Magic.toPointer(ref loc), value, mask);
        }

        [Inline]
        protected override void WriteImplByRef(ref UIntPtr loc,
                                               UIntPtr value,
                                               int mask)
        {
            WriteImpl(Magic.toPointer(ref loc), value, mask);
        }

        [Inline]
        protected override void WriteImplByRef(ref float loc,
                                               float value,
                                               int mask)
        {
            WriteImpl(Magic.toPointer(ref loc), value, mask);
        }

        [Inline]
        protected override void WriteImplByRef(ref double loc,
                                               double value,
                                               int mask)
        {
            WriteImpl(Magic.toPointer(ref loc), value, mask);
        }

        // this method is NOT expected to invoke either the source or
        // target barrier.
        [AssertDevirtualize]
        protected abstract bool WeakCASWordSlow(Object o,
                                                UIntPtr offset,
                                                UIntPtr mask,
                                                UIntPtr shiftedValue,
                                                UIntPtr shiftedComparand,
                                                bool isObject);

        // returns the shifted result.  does not guarantee the correctness
        // of the result for anything but the bits in the mask.
        [NoInline]
        [CalledRarely]
        static UIntPtr StrongCASWordSlow(Object o,
                                         UIntPtr offset,
                                         UIntPtr mask,
                                         UIntPtr shiftedValue,
                                         UIntPtr shiftedComparand,
                                         bool isObject)
        {
            if (fVerbose && DebugThread) {
                VTable.DebugPrint("StrongCASWordSlow: o = ");
                VTable.DebugPrint((ulong)Magic.addressOf(o));
                VTable.DebugPrint(", offset = ");
                VTable.DebugPrint((ulong)offset);
                VTable.DebugPrint(", mask = ");
                VTable.DebugPrint((ulong)mask);
                VTable.DebugPrint(", shiftedValue = ");
                VTable.DebugPrint((ulong)shiftedValue);
                VTable.DebugPrint(", shiftedComparand = ");
                VTable.DebugPrint((ulong)shiftedComparand);
                VTable.DebugPrint("\n");
            }
            for (;;) {
                UIntPtr oldVal=laInstance.ReadWordSlow(o, offset);
                if (fVerbose && DebugThread) {
                    VTable.DebugPrint("StrongCASWordSlow: oldVal = ");
                    VTable.DebugPrint((ulong)oldVal);
                    VTable.DebugPrint("\n");
                }
                if (!EqImpl(oldVal&mask,
                            shiftedComparand&mask,
                            isObject) ||
                    laInstance.WeakCASWordSlow(o, offset, mask,
                                             shiftedValue, oldVal,
                                             isObject)) {
                    return oldVal;
                }
            }
        }

        [NoInline]
        [CalledRarely]
        static UIntPtr StrongXCHGWordSlow(Object o,
                                          UIntPtr offset,
                                          UIntPtr mask,
                                          UIntPtr shiftedValue,
                                          bool isObject)
        {
            for (;;) {
                UIntPtr oldVal=laInstance.ReadWordSlow(o, offset);
                if (laInstance.WeakCASWordSlow(o, offset, mask,
                                             shiftedValue, oldVal,
                                             isObject)) {
                    return oldVal;
                }
            }
        }

        [AssertDevirtualize]
        protected abstract bool WeakCASArbitrarySlow(Object o,
                                                     UIntPtr offset,
                                                     UIntPtr size,
                                                     ulong value,
                                                     ulong comparand);

        [NoInline]
        [CalledRarely]
        static ulong StrongCASArbitrarySlow(Object o,
                                            UIntPtr offset,
                                            UIntPtr size,
                                            ulong value,
                                            ulong comparand)
        {
            for (;;) {
                ulong oldVal=LoadSlow(o, offset, size);
                if (oldVal!=comparand) {
                    if (laInstance.WeakCASArbitrarySlow(o, offset, size,
                                                      oldVal, oldVal)) {
                        return oldVal;
                    }
                } else if (laInstance.WeakCASArbitrarySlow(o, offset, size,
                                                         value, comparand)) {
                    return oldVal;
                }
            }
        }

        [NoInline]
        [CalledRarely]
        static ulong StrongXCHGArbitrarySlow(Object o,
                                             UIntPtr offset,
                                             UIntPtr size,
                                             ulong value)
        {
            for (;;) {
                ulong oldVal=LoadSlow(o, offset, size);
                if (laInstance.WeakCASArbitrarySlow(o, offset, size,
                                                  value, oldVal)) {
                    return oldVal;
                }
            }
        }

        [NoInline]
        [CalledRarely]
        internal static UIntPtr
        AtomicCompareAndSwapObjSlow(UIntPtr *ptr,
                                    UIntPtr newValueBits,
                                    UIntPtr comparandBits)
        {
            if (fCount) {
                numAtomics++;
            }
            UIntPtr result;
            UIntPtr addr=(UIntPtr)ptr;
            UIntPtr baseAddr=baseAddr = FindObjectForPreInteriorPtr(addr);
            if (baseAddr == UIntPtr.Zero) {
                TargetBarrierWithForward(*ptr);
                result=
                    Interlocked.CompareExchange(ptr,
                                                newValueBits,
                                                comparandBits);
            } else {
                Object o=Magic.fromAddress(baseAddr);
                TargetBarrierWithForward(laInstance.ReadWordSlow(o, addr-baseAddr));
                result=StrongCASWordSlow(o, addr-baseAddr,
                                         UIntPtr.MaxValue,
                                         newValueBits,
                                         comparandBits,
                                         true /* isObject */);
            }
            return result;
        }

        [Inline]
        protected override Object
        AtomicCompareAndSwapImpl(ref Object reference,
                                 Object newValue,
                                 Object comparand,
                                 int mask)
        {
            UIntPtr newValueBits = Magic.addressOf(newValue);
            UIntPtr comparandBits = Magic.addressOf(comparand);

            SourceBarrierWithForward(newValueBits);

            UIntPtr result;

            UIntPtr *ptr=Magic.toPointer(ref reference);
            if (AllowFastPath(mask)) {
                TargetBarrierNoForward(*ptr);
                result=
                    Interlocked.CompareExchange(ptr,
                                                newValueBits,
                                                comparandBits);
            } else {
                result=AtomicCompareAndSwapObjSlow(ptr,
                                                   newValueBits,
                                                   comparandBits);
            }

            if (StrictlyAllowFastPath(mask)) {
                return Magic.fromAddress(result);
            } else {
                return ToSpaceAsObj(result);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static UIntPtr AtomicSwapObjSlow(UIntPtr *ptr,
                                                  UIntPtr newValueBits)
        {
            if (fCount) {
                numAtomics++;
            }
            UIntPtr result;
            UIntPtr addr=(UIntPtr)ptr;
            UIntPtr baseAddr = FindObjectForPreInteriorPtr(addr);
            if (baseAddr == UIntPtr.Zero) {
                TargetBarrierWithForward(*ptr);
                result=
                    Interlocked.Exchange(ptr,
                                         newValueBits);
            } else {
                Object o=Magic.fromAddress(baseAddr);
                TargetBarrierWithForward(laInstance.ReadWordSlow(o, addr-baseAddr));
                result=StrongXCHGWordSlow(o, addr-baseAddr,
                                          UIntPtr.MaxValue,
                                          newValueBits,
                                          true);
            }
            return result;
        }

        [Inline]
        protected override Object AtomicSwapImpl(ref Object reference,
                                                 Object newValue,
                                                 int mask)
        {
            UIntPtr newValueBits=Magic.addressOf(newValue);

            SourceBarrierWithForward(newValueBits);

            UIntPtr result;

            UIntPtr *ptr=Magic.toPointer(ref reference);
            if (AllowFastPath(mask)) {
                TargetBarrierNoForward(*ptr);
                result=
                    Interlocked.Exchange(ptr,
                                         newValueBits);
            } else {
                result=AtomicSwapObjSlow(ptr, newValueBits);
            }

            if (StrictlyAllowFastPath(mask)) {
                return Magic.fromAddress(result);
            } else {
                return ToSpaceAsObj(result);
            }
        }

        static ulong StrongCASSlow(Object o,
                                   UIntPtr offset,
                                   UIntPtr size,
                                   ulong value,
                                   ulong comparand)
        {
            if (fVerbose && DebugThread) {
                VTable.DebugPrint("StrongCASSlow: offset = ");
                VTable.DebugPrint((ulong)offset);
                VTable.DebugPrint(", size = ");
                VTable.DebugPrint((ulong)size);
                VTable.DebugPrint("\n");
            }

            UIntPtr maxLowOff=(UIntPtr)sizeof(UIntPtr);
            UIntPtr lowMask=maxLowOff-1;
            UIntPtr lowOff=offset&lowMask;
            offset&=~lowMask;
            if (lowOff+size>maxLowOff) {
                if (fVerbose && DebugThread) {
                    VTable.DebugPrint("StrongCASSlow: WEIRD! we're using arbitrary-slow CAS.\n");
                }
                return StrongCASArbitrarySlow(o, offset, size,
                                              value, comparand);
            } else {
                return UnShiftMask(StrongCASWordSlow(o, offset,
                                                     MakeMask(lowOff,
                                                              size),
                                                     Shift(value,
                                                           lowOff),
                                                     Shift(comparand,
                                                           lowOff),
                                                     false /* not isObject */),
                                   lowOff, size);
            }
        }

        static ulong StrongCASSlow(Object o,
                                   UIntPtr offset,
                                   int size,
                                   ulong value,
                                   ulong comparand)
        {
            return StrongCASSlow(o, offset, (UIntPtr)size,
                                 value, comparand);
        }

        static ulong StrongXCHGSlow(Object o,
                                    UIntPtr offset,
                                    UIntPtr size,
                                    ulong value)
        {
            UIntPtr maxLowOff=(UIntPtr)sizeof(UIntPtr);
            UIntPtr lowMask=maxLowOff-1;
            UIntPtr lowOff=offset&lowMask;
            offset&=~lowMask;
            if (lowOff+size>maxLowOff) {
                return StrongXCHGArbitrarySlow(o, offset, size,
                                               value);
            } else {
                return UnShiftMask(StrongXCHGWordSlow(o, offset,
                                                      MakeMask(lowOff,
                                                               size),
                                                      Shift(value,
                                                            lowOff),
                                                      false /* not object */),
                                   lowOff, size);
            }
        }

        static ulong StrongXCHGSlow(Object o,
                                    UIntPtr offset,
                                    int size,
                                    ulong value)
        {
            return StrongXCHGSlow(o, offset, (UIntPtr)size, value);
        }

        [NoInline]
        [CalledRarely]
        internal static int AtomicCompareAndSwapSlow(int *ptr,
                                                     int value,
                                                     int comparand)
        {
            if (fCount) {
                numAtomics++;
            }
            UIntPtr addr=(UIntPtr)ptr;
            UIntPtr baseAddr = FindObjectForPreInteriorPtr(addr);
            if (baseAddr == UIntPtr.Zero) {
                return Interlocked.CompareExchange(ptr, value, comparand);
            } else {
                return (int)StrongCASSlow(Magic.fromAddress(baseAddr),
                                          addr-baseAddr,
                                          4,
                                          (ulong)value,
                                          (ulong)comparand);
            }
        }

        [Inline]
        protected override int
        AtomicCompareAndSwapImpl(ref int reference,
                                 int value,
                                 int comparand,
                                 int mask)
        {
            int *ptr=Magic.toPointer(ref reference);
            if (AllowIdleFastPath(mask)) {
                return Interlocked.CompareExchange(ptr, value, comparand);
            } else {
                return AtomicCompareAndSwapSlow(ptr, value, comparand);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static int AtomicSwapSlow(int *ptr,
                                           int value)
        {
            if (fCount) {
                numAtomics++;
            }
            UIntPtr addr=(UIntPtr)ptr;
            UIntPtr baseAddr = FindObjectForPreInteriorPtr(addr);
            if (baseAddr == UIntPtr.Zero) {
                return Interlocked.Exchange(ptr, value);
            } else {
                return (int)StrongXCHGSlow(Magic.fromAddress(baseAddr),
                                           addr-baseAddr,
                                           4,
                                           (ulong)value);
            }
        }

        [Inline]
        protected override int AtomicSwapImpl(ref int reference,
                                              int value,
                                              int mask)
        {
            int *ptr=Magic.toPointer(ref reference);
            if (AllowIdleFastPath(mask)) {
                return Interlocked.Exchange(ptr, value);
            } else {
                return AtomicSwapSlow(ptr, value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static long AtomicCompareAndSwapSlow(long *ptr,
                                                      long value,
                                                      long comparand)
        {
            if (fCount) {
                numAtomics++;
            }
            UIntPtr addr=(UIntPtr)ptr;
            UIntPtr baseAddr = FindObjectForPreInteriorPtr(addr);
            if (baseAddr == UIntPtr.Zero) {
                return Interlocked.CompareExchange(ptr, value, comparand);
            } else {
                return (long)StrongCASSlow(Magic.fromAddress(baseAddr),
                                           addr-baseAddr,
                                           8,
                                           (ulong)value,
                                           (ulong)comparand);
            }
        }

        [Inline]
        protected override long
        AtomicCompareAndSwapImpl(ref long reference,
                                 long value,
                                 long comparand,
                                 int mask)
        {
            long *ptr=Magic.toPointer(ref reference);
            UIntPtr addr=(UIntPtr)ptr;
            if (AllowIdleFastPath(mask)) {
                return Interlocked.CompareExchange(ptr, value, comparand);
            } else {
                return AtomicCompareAndSwapSlow(ptr, value, comparand);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static UIntPtr AtomicCompareAndSwapSlow(UIntPtr *ptr,
                                                         UIntPtr value,
                                                         UIntPtr comparand)
        {
            if (fCount) {
                numAtomics++;
            }
            UIntPtr addr=(UIntPtr)ptr;
            UIntPtr baseAddr = FindObjectForPreInteriorPtr(addr);
            if (baseAddr == UIntPtr.Zero) {
                return Interlocked.CompareExchange(ptr, value, comparand);
            } else {
                return (UIntPtr)StrongCASSlow(Magic.fromAddress(baseAddr),
                                              addr-baseAddr,
                                              UIntPtr.Size,
                                              (ulong)value,
                                              (ulong)comparand);
            }
        }

        [Inline]
        protected override UIntPtr
        AtomicCompareAndSwapImpl(ref UIntPtr reference,
                                 UIntPtr value,
                                 UIntPtr comparand,
                                 int mask)
        {
            UIntPtr *ptr=Magic.toPointer(ref reference);
            if (AllowIdleFastPath(mask)) {
                return Interlocked.CompareExchange(ptr, value, comparand);
            } else {
                return AtomicCompareAndSwapSlow(ptr, value, comparand);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static UIntPtr AtomicSwapSlow(UIntPtr *ptr,
                                               UIntPtr value)
        {
            if (fCount) {
                numAtomics++;
            }
            UIntPtr addr=(UIntPtr)ptr;
            UIntPtr baseAddr = FindObjectForPreInteriorPtr(addr);
            if (baseAddr == UIntPtr.Zero) {
                return Interlocked.Exchange(ptr, value);
            } else {
                return (UIntPtr)StrongXCHGSlow(Magic.fromAddress(baseAddr),
                                               addr-baseAddr,
                                               UIntPtr.Size,
                                               (ulong)value);
            }
        }

        [Inline]
        protected override UIntPtr AtomicSwapImpl(ref UIntPtr reference,
                                                  UIntPtr value,
                                                  int mask)
        {
            if (fCount) {
                numAtomics++;
            }
            UIntPtr *ptr=Magic.toPointer(ref reference);
            if (AllowIdleFastPath(mask)) {
                return Interlocked.Exchange(ptr, value);
            } else {
                return AtomicSwapSlow(ptr, value);
            }
        }

        protected override void CopyStructImpl(Object srcObj,
                                               Object dstObj,
                                               VTable vtable,
                                               UIntPtr srcPtr,
                                               UIntPtr dstPtr)
        {
            if (allowFastPath) {
                if (NeedsTargetBarrier) {
                    PreWriteStruct(vtable, dstPtr);
                }
                CopyStructNoBarrier(vtable, srcPtr, dstPtr);
            } else {
                if (fCount) {
                    numSlowCopyStructs++;
                }
                CopyStructWithSlowBarrier(srcObj, dstObj, vtable,
                                          srcPtr-Magic.addressOf(srcObj),
                                          dstPtr-Magic.addressOf(dstObj));
            }
        }

        protected override void CloneImpl(Object srcObject,
                                          Object dstObject)
        {
            if (allowFastPath) {
                // we're cloning, so nothing of note in the destination
                /*
                if (false && NeedsTargetBarrier) {
                    PreWriteObject(dstObject);
                }
                */
                CloneNoBarrier(srcObject, dstObject);
            } else {
                if (fCount) {
                    numSlowClones++;
                }
                CloneWithSlowBarrier(srcObject, dstObject);
            }
        }

        protected override void ArrayZeroImpl(Array array,
                                              int offset,
                                              int length)
        {
            if (allowFastPath) {
                if (NeedsTargetBarrier) {
                    PreWriteArray(array, offset, length);
                }
                ArrayZeroNoBarrier(array, offset, length);
            } else {
                if (fCount) {
                    numSlowArrayZeroes++;
                }
                ArrayZeroWithSlowBarrier(array, offset, length);
            }
        }

        protected override void ArrayCopyImpl(Array srcArray, int srcOffset,
                                              Array dstArray, int dstOffset,
                                              int length)
        {
            if (allowFastPath) {
                if (NeedsTargetBarrier) {
                    PreWriteArray(dstArray, dstOffset, length);
                }
                ArrayCopyNoBarrier(srcArray, srcOffset,
                                   dstArray, dstOffset,
                                   length);
            } else {
                if (fCount) {
                    numSlowArrayCopies++;
                }
                ArrayCopyWithSlowBarrier(srcArray, srcOffset,
                                         dstArray, dstOffset,
                                         length);
            }
        }

        [NoInline]
        [CalledRarely]
        static void StoreStaticFieldSlow(ref Object staticField,
                                         Object value)
        {
            UIntPtr *staticFieldAddr=(UIntPtr*)Magic.toPointer(ref staticField);
            TargetBarrierWithForward(*staticFieldAddr);
            UIntPtr valueAddr=Magic.addressOf(value);
            SourceBarrierWithForward(valueAddr);
            // NOTE: we don't have to forward value because before the
            // static data is scanned (and forwarded), we'll already have
            // instituted the to-space invariant.
            *staticFieldAddr = valueAddr;
        }

        [ForceInline]
        protected override void StoreStaticFieldImpl(ref Object staticField,
                                                     Object value,
                                                     int mask)
        {
            if (AllowFastPath(mask)) {
                UIntPtr *staticFieldAddr=(UIntPtr*)Magic.toPointer(ref staticField);
                UIntPtr valueAddr=Magic.addressOf(value);
                TargetAndSourceBarrierNoForward(staticFieldAddr, valueAddr);
                // NOTE: we don't have to forward value because before the
                // static data is scanned (and forwarded), we'll already have
                // instituted the to-space invariant.
                *staticFieldAddr = valueAddr;
            } else {
                StoreStaticFieldSlow(ref staticField, value);
            }
        }

        [NoInline]
        [CalledRarely]
        static Object LoadStaticFieldSlow(ref Object staticField)
        {
            return ToSpaceAsObj(staticField);
        }

        [Inline]
        [NoBarriers]
        protected override Object LoadStaticFieldImpl(ref Object staticField,
                                                      int mask)
        {
            if (AllowFastPath(mask)) {
                return staticField;
            } else {
                return LoadStaticFieldSlow(ref staticField);
            }
        }

        internal override void PinningEnabledHook()
        {
        }

        internal override bool PinOffsetPointers {
            [Inline]
            get { return false; }
        }

    }
}

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

    //[CCtorIsRunDuringStartup]
    //[NoBarriers]
    [NoCCtor]
    internal abstract unsafe class Barrier
    {

        [TrustedNonNull]
        [NoBarriers]
        protected internal static Barrier installedBarrier;

        [TrustedNonNull]
        private static CopyFieldsVisitor copyFieldsVisitor;

        [TrustedNonNull]
        private static ZeroFieldsVisitor zeroFieldsVisitor;

        [TrustedNonNull]
        private static SlowCopyFieldsVisitor slowCopyFieldsVisitor;

        [TrustedNonNull]
        private static SlowZeroFieldsVisitor slowZeroFieldsVisitor;

        [NoBarriers]
        [NoHeapAllocation]
        internal static void PreInitialize()
        {
#if !SINGULARITY || CONCURRENT_MS_COLLECTOR
            if (GC.wbType == WBType.CMS) {
                // We need a write barrier even if we haven't set up enough of the memory
                // system to support allocating from bootstrap memory yet.
                installedBarrier = WriteBarrierCMS.MakeEarlyInstance();
            }
#endif
        }

        [NoBarriers]
        [PreInitRefCounts]
        internal static void Initialize()
        {
            switch (GC.wbType) {
#if !SINGULARITY || MARK_SWEEP_COLLECTOR || NULL_COLLECTOR
              case WBType.noWB: {
                  EmptyWriteBarrier.Initialize();
                  installedBarrier = EmptyWriteBarrier.instance;
                  break;
              }
#endif
#if !SINGULARITY || SEMISPACE_COLLECTOR || SLIDING_COLLECTOR || ADAPTIVE_COPYING_COLLECTOR
              case WBType.Generational: {
                  GenerationalWriteBarrier.Initialize();
                  installedBarrier = GenerationalWriteBarrier.instance;
                  break;
              }
#endif
#if !SINGULARITY || CONCURRENT_MS_COLLECTOR
              case WBType.CMS: {
                  WriteBarrierCMS.Initialize();
                  installedBarrier = WriteBarrierCMS.instance;
                  break;
              }
#endif
#if !SINGULARITY || ATOMIC_RC_COLLECTOR
              case WBType.ARC: {
                  AtomicRCWriteBarrier.Initialize();
                  installedBarrier = AtomicRCWriteBarrier.instance;
                  break;
              }
#endif
#if !SINGULARITY || SEMISPACE_COLLECTOR || SLIDING_COLLECTOR || ADAPTIVE_COPYING_COLLECTOR
              case WBType.AllCards: {
                  AllCardsWriteBarrier.Initialize();
                  installedBarrier = AllCardsWriteBarrier.instance;
                  break;
              }
#endif
#if !SINGULARITY
              case WBType.ExpandingCoCo: {
                  ExpandingCoCoBarrier.Initialize();
                  installedBarrier = ExpandingCoCoBarrier.instance;
                  break;
              }
              case WBType.ProbabilisticCoCo: {
                  ProbabilisticCoCoBarrier.Initialize();
                  installedBarrier = ProbabilisticCoCoBarrier.instance;
                  break;
              }
              case WBType.AbortingCoCo: {
                  AbortingCoCoBarrier.Initialize();
                  installedBarrier = AbortingCoCoBarrier.instance;
                  break;
              }
              case WBType.BrooksTest: {
                  BrooksBarrierTest.Initialize();
                  installedBarrier = BrooksBarrierTest.instance;
                  break;
              }
              case WBType.BrooksCMSTest: {
                  BrooksCMSBarrierTest.Initialize();
                  installedBarrier = BrooksCMSBarrierTest.instance;
                  break;
              }
#endif
              default: {
                  VTable.NotReached("Unknown write barrier type: "+GC.wbType);
                  break;
              }
            }
            // copyFieldsVisitor = new CopyFieldsVisitor();
            Barrier.copyFieldsVisitor = (CopyFieldsVisitor)
                BootstrapMemory.Allocate(typeof(CopyFieldsVisitor));
            // zeroFieldsVisitor = new ZeroFieldsVisitor();
            Barrier.zeroFieldsVisitor = (ZeroFieldsVisitor)
                BootstrapMemory.Allocate(typeof(ZeroFieldsVisitor));
            // slowCopyFieldsVisitor = new SlowCopyFieldsVisitor();
            Barrier.slowCopyFieldsVisitor = (SlowCopyFieldsVisitor)
                BootstrapMemory.Allocate(typeof(SlowCopyFieldsVisitor));
            // slowZeroFieldsVisitor = new SlowZeroFieldsVisitor();
            Barrier.slowZeroFieldsVisitor = (SlowZeroFieldsVisitor)
                BootstrapMemory.Allocate(typeof(SlowZeroFieldsVisitor));
        }

        // NOTE: this code uses ForceInline instead of Inline to indicate that
        // inlining should occur even if the caller is huge.  In general, this
        // attribute should be used with great care.  DO NOT USE IT ELSEWHERE IN
        // THE RUNTIME UNLESS YOU ARE WILLING TO DOCUMENT YOUR USE IN
        // IrSimpleInliner.cs AND Attributes.cs!  AND NEVER USE IT IN
        // APPLICATION OR OS CODE!

        //////////////////////// StoreIndirectImpl /////////////////////

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImplByRef(ref Object location,
                                                      Object value,
                                                      int mask)
        {
            this.WriteImplByRef(ref location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImplByRef(ref float location,
                                                      float value,
                                                      int mask)
        {
            this.WriteImplByRef(ref location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImplByRef(ref double location,
                                                      double value,
                                                      int mask)
        {
            this.WriteImplByRef(ref location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImplByRef(ref byte location,
                                                      byte value,
                                                      int mask)
        {
            this.WriteImplByRef(ref location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImplByRef(ref ushort location,
                                                      ushort value,
                                                      int mask)
        {
            this.WriteImplByRef(ref location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImplByRef(ref uint location,
                                                      uint value,
                                                      int mask)
        {
            this.WriteImplByRef(ref location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImplByRef(ref ulong location,
                                                      ulong value,
                                                      int mask)
        {
            this.WriteImplByRef(ref location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImplByRef(ref UIntPtr location,
                                                      UIntPtr value,
                                                      int mask)
        {
            this.WriteImplByRef(ref location, value, mask);
        }

        //////////////////////// StoreIndirectImpl to ptr /////////////////////

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImpl(UIntPtr* location,
                                                 Object value,
                                                 int mask)
        {
            this.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImpl(float* location,
                                                 float value,
                                                 int mask)
        {
            this.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImpl(double* location,
                                                 double value,
                                                 int mask)
        {
            this.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImpl(byte* location,
                                                 byte value,
                                                 int mask)
        {
            this.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImpl(ushort* location,
                                                 ushort value,
                                                 int mask)
        {
            this.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImpl(uint* location,
                                                 uint value,
                                                 int mask)
        {
            this.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImpl(ulong* location,
                                                 ulong value,
                                                 int mask)
        {
            this.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreIndirectImpl(UIntPtr* location,
                                                 UIntPtr value,
                                                 int mask)
        {
            this.WriteImpl(location, value, mask);
        }

        //////////////////////// LoadIndirectImpl from ptr /////////////////////

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual Object LoadObjIndirectImpl(UIntPtr* location,
                                                     int mask)
        {
            return this.ReadObjImpl(location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual float LoadIndirectImpl(float* location,
                                                 int mask)
        {
            return this.ReadImpl(location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual double LoadIndirectImpl(double* location,
                                                  int mask)
        {
            return this.ReadImpl(location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual byte LoadIndirectImpl(byte* location,
                                                int mask)
        {
            return this.ReadImpl(location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual ushort LoadIndirectImpl(ushort* location,
                                                  int mask)
        {
            return this.ReadImpl(location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual uint LoadIndirectImpl(uint* location,
                                                int mask)
        {
            return this.ReadImpl(location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual ulong LoadIndirectImpl(ulong* location,
                                                 int mask)
        {
            return this.ReadImpl(location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual UIntPtr LoadIndirectImpl(UIntPtr* location,
                                                   int mask)
        {
            return this.ReadImpl(location, mask);
        }

        //////////////////////// LoadIndirectImpl /////////////////////

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual Object LoadIndirectImplByRef(ref Object location,
                                                       int mask)
        {
            return this.ReadImplByRef(ref location, mask);
        }

        [Inline]
        [NoBarriers]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual float LoadIndirectImplByRef(ref float location,
                                                      int mask)
        {
            return this.ReadImplByRef(ref location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual double LoadIndirectImplByRef(ref double location,
                                                       int mask)
        {
            return this.ReadImplByRef(ref location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual byte LoadIndirectImplByRef(ref byte location,
                                                     int mask)
        {
            return this.ReadImplByRef(ref location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual ushort LoadIndirectImplByRef(ref ushort location,
                                                       int mask)
        {
            return this.ReadImplByRef(ref location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual uint LoadIndirectImplByRef(ref uint location,
                                                     int mask)
        {
            return this.ReadImplByRef(ref location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual ulong LoadIndirectImplByRef(ref ulong location,
                                                      int mask)
        {
            return this.ReadImplByRef(ref location, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual UIntPtr LoadIndirectImplByRef(ref UIntPtr location,
                                                        int mask)
        {
            return this.ReadImplByRef(ref location, mask);
        }

        /////////////////////// StoreObjectFieldImpl ///////////////////

        [ForceInline]
        [NoBarriers]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual void StoreObjectFieldImpl(Object obj,
                                                    UIntPtr fieldOffset,
                                                    Object value,
                                                    int mask)
        {
            this.WriteImpl(obj, fieldOffset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreObjectFieldImpl(Object obj,
                                                    UIntPtr fieldOffset,
                                                    float value,
                                                    int mask)
        {
            this.WriteImpl(obj, fieldOffset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreObjectFieldImpl(Object obj,
                                                    UIntPtr fieldOffset,
                                                    double value,
                                                    int mask)
        {
            this.WriteImpl(obj, fieldOffset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreObjectFieldImpl(Object obj,
                                                    UIntPtr fieldOffset,
                                                    byte value,
                                                    int mask)
        {
            this.WriteImpl(obj, fieldOffset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreObjectFieldImpl(Object obj,
                                                    UIntPtr fieldOffset,
                                                    ushort value,
                                                    int mask)
        {
            this.WriteImpl(obj, fieldOffset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreObjectFieldImpl(Object obj,
                                                    UIntPtr fieldOffset,
                                                    uint value,
                                                    int mask)
        {
            this.WriteImpl(obj, fieldOffset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreObjectFieldImpl(Object obj,
                                                    UIntPtr fieldOffset,
                                                    ulong value,
                                                    int mask)
        {
            this.WriteImpl(obj, fieldOffset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreObjectFieldImpl(Object obj,
                                                    UIntPtr fieldOffset,
                                                    UIntPtr value,
                                                    int mask)
        {
            this.WriteImpl(obj, fieldOffset, value, mask);
        }

        /////////////////////// LoadObjectFieldImpl ///////////////////

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual Object LoadObjObjectFieldImpl(Object obj,
                                                        UIntPtr fieldOffset,
                                                        int mask)
        {
            return this.ReadObjImpl(obj, fieldOffset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual float LoadFloatObjectFieldImpl(Object obj,
                                                         UIntPtr fieldOffset,
                                                         int mask)
        {
            return this.ReadFloatImpl(obj, fieldOffset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual double LoadDoubleObjectFieldImpl(Object obj,
                                                           UIntPtr fieldOffset,
                                                           int mask)
        {
            return this.ReadDoubleImpl(obj, fieldOffset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual byte LoadByteObjectFieldImpl(Object obj,
                                                       UIntPtr fieldOffset,
                                                       int mask)
        {
            return this.ReadByteImpl(obj, fieldOffset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual ushort LoadUShortObjectFieldImpl(Object obj,
                                                           UIntPtr fieldOffset,
                                                           int mask)
        {
            return this.ReadUShortImpl(obj, fieldOffset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual uint LoadUIntObjectFieldImpl(Object obj,
                                                       UIntPtr fieldOffset,
                                                       int mask)
        {
            return this.ReadUIntImpl(obj, fieldOffset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual ulong LoadULongObjectFieldImpl(Object obj,
                                                         UIntPtr fieldOffset,
                                                         int mask)
        {
            return this.ReadULongImpl(obj, fieldOffset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        UIntPtr LoadUIntPtrObjectFieldImpl(Object obj,
                                           UIntPtr fieldOffset,
                                           int mask)
        {
            return this.ReadUIntPtrImpl(obj, fieldOffset, mask);
        }

        ////////////////////// StoreStructFieldImpl ////////////////////

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreStructFieldImpl(UIntPtr structPtr,
                                                    UIntPtr fieldOffset,
                                                    Object value,
                                                    int mask)
        {
            UIntPtr *fieldPtr = (UIntPtr *) (structPtr + fieldOffset);
            this.WriteImpl(fieldPtr, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreStructFieldImpl(UIntPtr structPtr,
                                                    UIntPtr fieldOffset,
                                                    float value,
                                                    int mask)
        {
            float *fieldPtr = (float *) (structPtr + fieldOffset);
            this.WriteImpl(fieldPtr, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreStructFieldImpl(UIntPtr structPtr,
                                                    UIntPtr fieldOffset,
                                                    double value,
                                                    int mask)
        {
            double *fieldPtr = (double *) (structPtr + fieldOffset);
            this.WriteImpl(fieldPtr, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreStructFieldImpl(UIntPtr structPtr,
                                                    UIntPtr fieldOffset,
                                                    byte value,
                                                    int mask)
        {
            byte *fieldPtr = (byte *) (structPtr + fieldOffset);
            this.WriteImpl(fieldPtr, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreStructFieldImpl(UIntPtr structPtr,
                                                    UIntPtr fieldOffset,
                                                    ushort value,
                                                    int mask)
        {
            ushort *fieldPtr = (ushort *) (structPtr + fieldOffset);
            this.WriteImpl(fieldPtr, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreStructFieldImpl(UIntPtr structPtr,
                                                    UIntPtr fieldOffset,
                                                    uint value,
                                                    int mask)
        {
            uint *fieldPtr = (uint *) (structPtr + fieldOffset);
            this.WriteImpl(fieldPtr, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreStructFieldImpl(UIntPtr structPtr,
                                                    UIntPtr fieldOffset,
                                                    ulong value,
                                                    int mask)
        {
            ulong *fieldPtr = (ulong *) (structPtr + fieldOffset);
            this.WriteImpl(fieldPtr, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreStructFieldImpl(UIntPtr structPtr,
                                                    UIntPtr fieldOffset,
                                                    UIntPtr value,
                                                    int mask)
        {
            UIntPtr *fieldPtr = (UIntPtr *) (structPtr + fieldOffset);
            this.WriteImpl(fieldPtr, value, mask);
        }

        //////////////////// LoadStructFieldImpl ////////////////////

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual Object LoadObjStructFieldImpl(UIntPtr structPtr,
                                                        UIntPtr fieldOffset,
                                                        int mask)
        {
            UIntPtr *fieldPtr = (UIntPtr *) (structPtr + fieldOffset);
            return this.ReadObjImpl(fieldPtr, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual float LoadFloatStructFieldImpl(UIntPtr structPtr,
                                                         UIntPtr fieldOffset,
                                                         int mask)
        {
            float *fieldPtr = (float *) (structPtr + fieldOffset);
            return this.ReadImpl(fieldPtr, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual double LoadDoubleStructFieldImpl(UIntPtr structPtr,
                                                           UIntPtr fieldOffset,
                                                           int mask)
        {
            double *fieldPtr = (double *) (structPtr + fieldOffset);
            return this.ReadImpl(fieldPtr, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual byte LoadByteStructFieldImpl(UIntPtr structPtr,
                                                       UIntPtr fieldOffset,
                                                       int mask)
        {
            byte *fieldPtr = (byte *) (structPtr + fieldOffset);
            return this.ReadImpl(fieldPtr, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual ushort LoadUShortStructFieldImpl(UIntPtr structPtr,
                                                           UIntPtr fieldOffset,
                                                           int mask)
        {
            ushort *fieldPtr = (ushort *) (structPtr + fieldOffset);
            return this.ReadImpl(fieldPtr, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual uint LoadUIntStructFieldImpl(UIntPtr structPtr,
                                                       UIntPtr fieldOffset,
                                                       int mask)
        {
            uint *fieldPtr = (uint *) (structPtr + fieldOffset);
            return this.ReadImpl(fieldPtr, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual ulong LoadULongStructFieldImpl(UIntPtr structPtr,
                                                         UIntPtr fieldOffset,
                                                         int mask)
        {
            ulong *fieldPtr = (ulong *) (structPtr + fieldOffset);
            return this.ReadImpl(fieldPtr, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        UIntPtr LoadUIntPtrStructFieldImpl(UIntPtr structPtr,
                                           UIntPtr fieldOffset,
                                           int mask)
        {
            UIntPtr *fieldPtr = (UIntPtr *) (structPtr + fieldOffset);
            return this.ReadImpl(fieldPtr, mask);
        }

        //////////////////// StoreVectorElementImpl ////////////////////

        [ForceInline]
        [NoBarriers]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual void StoreVectorElementImpl(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      Object value,
                                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(vector, offset, value, mask);

        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreVectorElementImpl(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      float value,
                                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(vector, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreVectorElementImpl(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      double value,
                                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(vector, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual void StoreVectorElementImpl(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      byte value,
                                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(vector, offset, value, mask);
        }

        [Inline]
        [AssertDevirtualize]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        protected virtual void StoreVectorElementImpl(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      ushort value,
                                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(vector, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreVectorElementImpl(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      uint value,
                                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(vector, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreVectorElementImpl(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      ulong value,
                                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(vector, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreVectorElementImpl(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      UIntPtr value,
                                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(vector, offset, value, mask);
        }

        //////////////////// LoadVectorElementImpl ////////////////////

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual Object LoadObjVectorElementImpl(Array vector,
                                                          int index,
                                                          int arrayElementSize,
                                                          UIntPtr fieldOffset,
                                                          int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadObjImpl(vector, offset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        float LoadFloatVectorElementImpl(Array vector,
                                         int index,
                                         int arrayElementSize,
                                         UIntPtr fieldOffset,
                                         int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadFloatImpl(vector, offset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        double LoadDoubleVectorElementImpl(Array vector,
                                           int index,
                                           int arrayElementSize,
                                           UIntPtr fieldOffset,
                                           int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadDoubleImpl(vector, offset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        byte LoadByteVectorElementImpl(Array vector,
                                       int index,
                                       int arrayElementSize,
                                       UIntPtr fieldOffset,
                                       int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadByteImpl(vector, offset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        ushort LoadUShortVectorElementImpl(Array vector,
                                           int index,
                                           int arrayElementSize,
                                           UIntPtr fieldOffset,
                                           int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadUShortImpl(vector, offset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        uint LoadUIntVectorElementImpl(Array vector,
                                       int index,
                                       int arrayElementSize,
                                       UIntPtr fieldOffset,
                                       int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadUIntImpl(vector, offset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        ulong LoadULongVectorElementImpl(Array vector,
                                         int index,
                                         int arrayElementSize,
                                         UIntPtr fieldOffset,
                                         int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadULongImpl(vector, offset, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        UIntPtr LoadUIntPtrVectorElementImpl(Array vector,
                                             int index,
                                             int arrayElementSize,
                                             UIntPtr fieldOffset,
                                             int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadUIntPtrImpl(vector, offset, mask);
        }

        //////////////////// StoreArrayElementImpl ////////////////////

        [ForceInline]
        [NoBarriers]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual void StoreArrayElementImpl(Array array,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     Object value,
                                                     int mask)
        {
            UIntPtr offset = IndexedFieldOffset(array, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(array, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreArrayElementImpl(Array array,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     float value,
                                                     int mask)
        {
            UIntPtr offset = IndexedFieldOffset(array, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(array, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreArrayElementImpl(Array array,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     double value,
                                                     int mask)
        {
            UIntPtr offset = IndexedFieldOffset(array, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(array, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreArrayElementImpl(Array array,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     byte value,
                                                     int mask)
        {
            UIntPtr offset = IndexedFieldOffset(array, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(array, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreArrayElementImpl(Array array,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     ushort value,
                                                     int mask)
        {
            UIntPtr offset = IndexedFieldOffset(array, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(array, offset, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreArrayElementImpl(Array array,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     uint value,
                                                     int mask)
        {
            UIntPtr offset = IndexedFieldOffset(array, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(array, offset, value, mask);
        }

        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual void StoreArrayElementImpl(Array array,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     ulong value,
                                                     int mask)
        {
            UIntPtr offset = IndexedFieldOffset(array, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(array, offset, value, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual void StoreArrayElementImpl(Array array,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     UIntPtr value,
                                                     int mask)
        {
            UIntPtr offset = IndexedFieldOffset(array, index,
                                                arrayElementSize, fieldOffset);
            this.WriteImpl(array, offset, value, mask);
        }

        //////////////////// LoadArrayElementImpl ////////////////////

        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual Object LoadObjArrayElementImpl(Array vector,
                                                         int index,
                                                         int arrayElementSize,
                                                         UIntPtr fieldOffset,
                                                         int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadObjImpl(vector, offset, mask);
        }

        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual
        float LoadFloatArrayElementImpl(Array vector,
                                        int index,
                                        int arrayElementSize,
                                        UIntPtr fieldOffset,
                                        int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadFloatImpl(vector, offset, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        double LoadDoubleArrayElementImpl(Array vector,
                                          int index,
                                          int arrayElementSize,
                                          UIntPtr fieldOffset,
                                          int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadDoubleImpl(vector, offset, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        byte LoadByteArrayElementImpl(Array vector,
                                      int index,
                                      int arrayElementSize,
                                      UIntPtr fieldOffset,
                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadByteImpl(vector, offset, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        ushort LoadUShortArrayElementImpl(Array vector,
                                          int index,
                                          int arrayElementSize,
                                          UIntPtr fieldOffset,
                                          int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadUShortImpl(vector, offset, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        uint LoadUIntArrayElementImpl(Array vector,
                                      int index,
                                      int arrayElementSize,
                                      UIntPtr fieldOffset,
                                      int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadUIntImpl(vector, offset, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected virtual
        ulong LoadULongArrayElementImpl(Array vector,
                                        int index,
                                        int arrayElementSize,
                                        UIntPtr fieldOffset,
                                        int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadULongImpl(vector, offset, mask);
        }

        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual
        UIntPtr LoadUIntPtrArrayElementImpl(Array vector,
                                            int index,
                                            int arrayElementSize,
                                            UIntPtr fieldOffset,
                                            int mask)
        {
            UIntPtr offset = IndexedFieldOffset(vector, index,
                                                arrayElementSize, fieldOffset);
            return this.ReadUIntPtrImpl(vector, offset, mask);
        }

        ////////////////// StoreStaticFieldImpl ///////////////////////

        [ForceInline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected virtual void StoreStaticFieldImpl(ref Object staticField,
                                                    Object value,
                                                    int mask)
        {
            this.WriteImplByRef(ref staticField, value, mask);
        }

        ////////////////// LoadStaticFieldImpl ///////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual Object LoadStaticFieldImpl(ref Object staticField,
                                                     int mask)
        {
            return this.ReadImplByRef(ref staticField, mask);
        }

        ///////////////////////// AtomicSwapImpl ///////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual Object AtomicSwapImpl(ref Object reference,
                                                Object value,
                                                int mask)
        {
            return Interlocked.Exchange(ref reference,value);
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual int AtomicSwapImpl(ref int reference,
                                             int value,
                                             int mask)
        {
            return Interlocked.Exchange(ref reference,value);
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual UIntPtr AtomicSwapImpl(ref UIntPtr reference,
                                                 UIntPtr value,
                                                 int mask)
        {
            return Interlocked.Exchange(ref reference,value);
        }

        ////////////////////// AtomicCompareAndSwapImpl ////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual Object
        AtomicCompareAndSwapImpl(ref Object reference,
                                 Object newValue,
                                 Object comparand,
                                 int mask)
        {
            return Interlocked.CompareExchange(ref reference,
                                               newValue,comparand);
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual int
        AtomicCompareAndSwapImpl(ref int reference,
                                 int newValue,
                                 int comparand,
                                 int mask)
        {
            return Interlocked.CompareExchange(ref reference,
                                               newValue, comparand);
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual long
        AtomicCompareAndSwapImpl(ref long reference,
                                 long newValue,
                                 long comparand,
                                 int mask)
        {
            return Interlocked.CompareExchange(ref reference,
                                               newValue, comparand);
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual UIntPtr
        AtomicCompareAndSwapImpl(ref UIntPtr reference,
                                 UIntPtr newValue,
                                 UIntPtr comparand,
                                 int mask)
        {
            return Interlocked.CompareExchange(ref reference,
                                               newValue, comparand);
        }

        /////////////////////////// ForwardImpl ///////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual Object ForwardImpl(Object o,int mask)
        {
            return o;
        }

        /////////////////////////// MemoryBarrierImpl ///////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual void MemoryBarrierImpl(int mask)
        {
#if !ARM && !ISA_ARM
            // HACK: MemoryBarrier is unimplemented in ARM
            // and causes compile-time failures when building
            // mscorlib in sepcomp mode. This change will break
            // CoCo if built with ARM.
            Thread.MemoryBarrier();
#endif
        }

        //////////////////////// PinImpl //////////////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual UIntPtr PinImpl(UIntPtr address,
                                          int mask)
        {
            return address;
        }

        /////////////////////// InitObjectImpl ////////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual void InitObjectImpl(Object o,VTable vtable)
        {
            MyInitObject(o, vtable);
        }

        [ForceInline]
        [NoBarriers]
        protected static void BootstrapInitObjectImpl(Object o, VTable vtable)
        {
            MyInitObject(o, vtable);
        }

        [ForceInline]
        [NoBarriers]
        private static void MyInitObject(Object o, VTable vtable)
        {
            o.vtable = vtable;
        }

        ///////////////////////// Weak Ref ////////////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual Object WeakRefReadImpl(UIntPtr addr, int mask)
        {
            return Magic.fromAddress(addr);
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual UIntPtr WeakRefWriteImpl(Object obj, int mask)
        {
            return Magic.addressOf(obj);
        }

        //////////////////////////// EqImpl ///////////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual bool EqImpl(Object a,Object b, int mask)
        {
            return a==b;
        }

        ////////////////////////// fast path selection ////////////////

        [ForceInline]
        [AssertDevirtualize]
        protected virtual bool AllowFastPathImpl()
        {
            return false;
        }

        ///////////////////////// CopyStructImpl ///////////////////////

        [AssertDevirtualize]
        [Inline]
        protected virtual void CopyStructImpl(Object srcObj,
                                              Object dstObj,
                                              VTable vtable,
                                              UIntPtr srcPtr,
                                              UIntPtr dstPtr)
        {
            CopyStructWithBarrier(vtable, srcPtr, dstPtr);
        }

        ////////////////////////// CloneImpl //////////////////////////

        [AssertDevirtualize]
        [Inline]
        protected virtual void CloneImpl(Object srcObject, Object dstObject)
        {
            CloneWithBarrier(srcObject, dstObject);
        }

        /////////////////////// ArrayZeroImpl /////////////////////////

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [AssertDevirtualize]
        [Inline]
        protected virtual void ArrayZeroImpl(Array array,
                                             int offset,
                                             int length)
        {
            ArrayZeroWithBarrier(array, offset, length);
        }

        /////////////////////// ArrayCopyImpl /////////////////////////

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [AssertDevirtualize]
        [Inline]
        protected virtual void ArrayCopyImpl(Array srcArray, int srcOffset,
                                             Array dstArray, int dstOffset,
                                             int length)
        {
            ArrayCopyWithBarrier(srcArray, srcOffset,
                                 dstArray, dstOffset,
                                 length);
        }

        ///////////////////// WriteImpl to ptr //////////////////////

        [AssertDevirtualize]
        [ForceInline]
        protected virtual void WriteImpl(UIntPtr *location,
                                         Object value,
                                         int mask)
        {
            *location = Magic.addressOf(value);
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual void WriteImpl(float *location,
                                         float value,
                                         int mask)
        {
            *location = value;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual void WriteImpl(double *location,
                                         double value,
                                         int mask)
        {
            *location = value;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual void WriteImpl(byte *location,
                                         byte value,
                                         int mask)
        {
            *location = value;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual void WriteImpl(ushort *location,
                                         ushort value,
                                         int mask)
        {
            *location = value;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual void WriteImpl(uint *location,
                                         uint value,
                                         int mask)
        {
            *location = value;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual void WriteImpl(ulong *location,
                                         ulong value,
                                         int mask)
        {
            *location = value;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual void WriteImpl(UIntPtr *location,
                                         UIntPtr value,
                                         int mask)
        {
            *location = value;
        }

        ////////////////////// WriteImpl to Object, pointer /////////////////

        [AssertDevirtualize]
        [ForceInline]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr *ptr,
                                         Object value,
                                         int mask)
        {
            this.WriteImpl(ptr, value, mask);
        }

        [AssertDevirtualize]
        [Inline]
        protected virtual void WriteImpl(Object o,
                                         float *ptr,
                                         float value,
                                         int mask)
        {
            this.WriteImpl(ptr, value, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         double *ptr,
                                         double value,
                                         int mask)
        {
            this.WriteImpl(ptr, value, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         byte *ptr,
                                         byte value,
                                         int mask)
        {
            this.WriteImpl(ptr, value, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         ushort *ptr,
                                         ushort value,
                                         int mask)
        {
            this.WriteImpl(ptr, value, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         uint *ptr,
                                         uint value,
                                         int mask)
        {
            this.WriteImpl(ptr, value, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         ulong *ptr,
                                         ulong value,
                                         int mask)
        {
            this.WriteImpl(ptr, value, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr *ptr,
                                         UIntPtr value,
                                         int mask)
        {
            this.WriteImpl(ptr, value, mask);
        }

        ///////////////////// WriteImpl to Object+offset //////////////////////

        [ForceInline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr offset,
                                         Object value,
                                         int mask)
        {
            this.WriteImpl(o,
                           (UIntPtr*)(Magic.addressOf(o)+offset),
                           value,
                           mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr offset,
                                         float value,
                                         int mask)
        {
            this.WriteImpl(o,
                           (float*)(Magic.addressOf(o)+offset),
                           value,
                           mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr offset,
                                         double value,
                                         int mask)
        {
            this.WriteImpl(o,
                           (double*)(Magic.addressOf(o)+offset),
                           value,
                           mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr offset,
                                         byte value,
                                         int mask)
        {
            this.WriteImpl(o,
                           (byte*)(Magic.addressOf(o)+offset),
                           value,
                           mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr offset,
                                         ushort value,
                                         int mask)
        {
            this.WriteImpl(o,
                           (ushort*)(Magic.addressOf(o)+offset),
                           value,
                           mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr offset,
                                         uint value,
                                         int mask)
        {
            this.WriteImpl(o,
                           (uint*)(Magic.addressOf(o)+offset),
                           value,
                           mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr offset,
                                         ulong value,
                                         int mask)
        {
            this.WriteImpl(o,
                           (ulong*)(Magic.addressOf(o)+offset),
                           value,
                           mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual void WriteImpl(Object o,
                                         UIntPtr offset,
                                         UIntPtr value,
                                         int mask)
        {
            this.WriteImpl(o,
                           (UIntPtr*)(Magic.addressOf(o)+offset),
                           value,
                           mask);
        }

        ///////////////////// WriteImpl to ref //////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual void WriteImplByRef(ref Object location,
                                              Object value,
                                              int mask)
        {
            location = value;
        }

        [AssertDevirtualize]
        [NoBarriers]
        [ForceInline]
        protected virtual void WriteImplByRef(ref float location,
                                              float value,
                                              int mask)
        {
            location = value;
        }

        [AssertDevirtualize]
        [NoBarriers]
        [ForceInline]
        protected virtual void WriteImplByRef(ref double location,
                                              double value,
                                              int mask)
        {
            location = value;
        }

        [AssertDevirtualize]
        [NoBarriers]
        [ForceInline]
        protected virtual void WriteImplByRef(ref byte location,
                                              byte value,
                                              int mask)
        {
            location = value;
        }

        [AssertDevirtualize]
        [NoBarriers]
        [ForceInline]
        protected virtual void WriteImplByRef(ref ushort location,
                                              ushort value,
                                              int mask)
        {
            location = value;
        }

        [AssertDevirtualize]
        [NoBarriers]
        [ForceInline]
        protected virtual void WriteImplByRef(ref uint location,
                                              uint value,
                                              int mask)
        {
            location = value;
        }

        [AssertDevirtualize]
        [NoBarriers]
        [ForceInline]
        protected virtual void WriteImplByRef(ref ulong location,
                                              ulong value,
                                              int mask)
        {
            location = value;
        }

        [AssertDevirtualize]
        [NoBarriers]
        [ForceInline]
        protected virtual void WriteImplByRef(ref UIntPtr location,
                                              UIntPtr value,
                                              int mask)
        {
            location = value;
        }

        ///////////////////// ReadImpl from ptr //////////////////////

        [AssertDevirtualize]
        [ForceInline]
        protected virtual Object ReadObjImpl(UIntPtr *location,
                                             int mask)
        {
            return Magic.fromAddress(*location);
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual float ReadImpl(float *location,
                                         int mask)
        {
            return *location;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual double ReadImpl(double *location,
                                          int mask)
        {
            return *location;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual byte ReadImpl(byte *location,
                                        int mask)
        {
            return *location;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual ushort ReadImpl(ushort *location,
                                          int mask)
        {
            return *location;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual uint ReadImpl(uint *location,
                                        int mask)
        {
            return *location;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual ulong ReadImpl(ulong *location,
                                         int mask)
        {
            return *location;
        }

        [AssertDevirtualize]
        [ForceInline]
        protected virtual UIntPtr ReadImpl(UIntPtr *location,
                                           int mask)
        {
            return *location;
        }

        ///////////////////// ReadImpl from Object, ptr ///////////////////

        [Inline]
        [AssertDevirtualize]
        protected virtual Object ReadObjImpl(Object o,
                                             UIntPtr *ptr,
                                             int mask)
        {
            return this.ReadObjImpl(ptr, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual float ReadImpl(Object o,
                                         float *ptr,
                                         int mask)
        {
            return this.ReadImpl(ptr, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual double ReadImpl(Object o,
                                          double *ptr,
                                          int mask)
        {
            return this.ReadImpl(ptr, mask);
        }

        [AssertDevirtualize]
        [Inline]
        protected virtual byte ReadImpl(Object o,
                                        byte *ptr,
                                        int mask)
        {
            return this.ReadImpl(ptr, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual ushort ReadImpl(Object o,
                                          ushort *ptr,
                                          int mask)
        {
            return this.ReadImpl(ptr, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual uint ReadImpl(Object o,
                                        uint *ptr,
                                        int mask)
        {
            return this.ReadImpl(ptr, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual ulong ReadImpl(Object o,
                                         ulong *ptr,
                                         int mask)
        {
            return this.ReadImpl(ptr, mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual UIntPtr ReadImpl(Object o,
                                           UIntPtr *ptr,
                                           int mask)
        {
            return this.ReadImpl(ptr, mask);
        }

        ///////////////////// ReadImpl from Object+off //////////////////////

        [Inline]
        [AssertDevirtualize]
        protected virtual Object ReadObjImpl(Object o,
                                             UIntPtr offset,
                                             int mask)
        {
            return this.ReadObjImpl(o,
                                    (UIntPtr*)(Magic.addressOf(o)+offset),
                                    mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual float ReadFloatImpl(Object o,
                                              UIntPtr offset,
                                              int mask)
        {
            return this.ReadImpl(o,
                                 (float*)(Magic.addressOf(o)+offset),
                                 mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual double ReadDoubleImpl(Object o,
                                                UIntPtr offset,
                                                int mask)
        {
            return this.ReadImpl(o,
                                 (double*)(Magic.addressOf(o)+offset),
                                 mask);
        }

        [AssertDevirtualize]
        [Inline]
        protected virtual byte ReadByteImpl(Object o,
                                            UIntPtr offset,
                                            int mask)
        {
            return this.ReadImpl(o,
                                 (byte*)(Magic.addressOf(o)+offset),
                                 mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual ushort ReadUShortImpl(Object o,
                                                UIntPtr offset,
                                                int mask)
        {
            return this.ReadImpl(o,
                                 (ushort*)(Magic.addressOf(o)+offset),
                                 mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual uint ReadUIntImpl(Object o,
                                            UIntPtr offset,
                                            int mask)
        {
            return this.ReadImpl(o,
                                 (uint*)(Magic.addressOf(o)+offset),
                                 mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual ulong ReadULongImpl(Object o,
                                              UIntPtr offset,
                                              int mask)
        {
            return this.ReadImpl(o,
                                 (ulong*)(Magic.addressOf(o)+offset),
                                 mask);
        }

        [Inline]
        [AssertDevirtualize]
        protected virtual UIntPtr ReadUIntPtrImpl(Object o,
                                                  UIntPtr offset,
                                                  int mask)
        {
            return this.ReadImpl(o,
                                 (UIntPtr*)(Magic.addressOf(o)+offset),
                                 mask);
        }

        ///////////////////// ReadImpl from ref //////////////////////

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual Object ReadImplByRef(ref Object location,
                                               int mask)
        {
            return location;
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual float ReadImplByRef(ref float location,
                                              int mask)
        {
            return location;
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual double ReadImplByRef(ref double location,
                                               int mask)
        {
            return location;
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual byte ReadImplByRef(ref byte location,
                                             int mask)
        {
            return location;
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual ushort ReadImplByRef(ref ushort location,
                                               int mask)
        {
            return location;
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual uint ReadImplByRef(ref uint location,
                                             int mask)
        {
            return location;
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual ulong ReadImplByRef(ref ulong location,
                                              int mask)
        {
            return location;
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected virtual UIntPtr ReadImplByRef(ref UIntPtr location,
                                                int mask)
        {
            return location;
        }

        /////////////////////// Helpers... //////////////////////////////

        [ForceInline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected static UIntPtr IndexedDataPtr(Array array) {
            return (UIntPtr) (Magic.addressOf(array) +
                              (array.vtable.baseLength-(uint)PreHeader.Size));
        }

        [ForceInline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected static UIntPtr IndexedFieldOffset(Array array,
                                                    int index,
                                                    int arrayElementSize,
                                                    UIntPtr fieldOffset)
        {
            return ((UIntPtr)(uint)index * (UIntPtr)(uint)arrayElementSize
                    + array.vtable.baseLength
                    + fieldOffset
                    - (UIntPtr)(uint)PreHeader.Size);
        }

        [ForceInline]
        [AssertDevirtualize]
        protected static UIntPtr IndexedElementOffset(Array array,
                                                      int index)
        {
            return (UIntPtr)(uint)index * (UIntPtr)(uint)array.vtable.arrayElementSize
                 + array.vtable.baseLength
                 - (UIntPtr)(uint)PreHeader.Size;
        }

        // copies a span of primitives from one object to another invoking
        // word-size read and write barriers along the way.
        // mostly useful as part of a greater implementation of struct,
        // object, or array copy in a GC that requires primitive barriers.
        // note that dstOff, srcOff, and nBytes must be word-aligned.
        // call this with great care.
        [Inline]
        protected static void MemCopyBarrierSlow(Object dst,
                                                 UIntPtr dstOff,
                                                 Object src,
                                                 UIntPtr srcOff,
                                                 UIntPtr nBytes) {
            for (;nBytes>0;nBytes-=sizeof(UIntPtr)) {
                installedBarrier
                    .WriteImpl(dst,dstOff,
                               installedBarrier.ReadUIntPtrImpl(src,srcOff,0),0);
                dstOff+=sizeof(UIntPtr);
                srcOff+=sizeof(UIntPtr);
            }
        }

        // Same as above but without knowledge of the object base.
        [Inline]
        protected static void MemCopyBarrierSlow(UIntPtr *dstPtr,
                                                 UIntPtr *srcPtr,
                                                 UIntPtr nBytes) {
            for (;nBytes>0;nBytes-=sizeof(UIntPtr)) {
                installedBarrier
                    .WriteImpl(dstPtr,installedBarrier.ReadImpl(srcPtr,0),0);
                dstPtr++;
                srcPtr++;
            }
        }

        // Really slow way of zeroing memory while invoking write
        // barriers.  Assumes that everything is word-aligned.
        [Inline]
        protected static void MemZeroBarrierSlow(Object dst,
                                                 UIntPtr dstOff,
                                                 UIntPtr nBytes) {
            for (;nBytes>0;nBytes-=sizeof(UIntPtr)) {
                installedBarrier.WriteImpl(dst,dstOff,UIntPtr.Zero,0);
                dstOff+=sizeof(UIntPtr);
            }
        }

        // Really slow way of zeroing memory while invoking write
        // barriers.  Assumes that everything is word-aligned.
        [Inline]
        protected static void MemZeroBarrierSlow(UIntPtr *dstPtr,
                                                 UIntPtr nBytes) {
            for (;nBytes>0;nBytes-=sizeof(UIntPtr)) {
                installedBarrier.WriteImpl(dstPtr,UIntPtr.Zero,0);
                dstPtr++;
            }
        }

        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected void CopyStructNoBarrier(VTable vtable,
                                           UIntPtr srcPtr,
                                           UIntPtr dstPtr)
        {
            int preHeaderSize = PreHeader.Size;
            int postHeaderSize = PostHeader.Size;
            int structSize = ((int) ObjectLayout.ObjectSize(vtable) -
                              (preHeaderSize + postHeaderSize));
            Buffer.MoveMemory((byte *) dstPtr, (byte *) srcPtr, structSize);
        }

        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected void CopyStructWithBarrier(VTable vtable,
                                             UIntPtr srcPtr,
                                             UIntPtr dstPtr)
        {
            copyFieldsVisitor.VisitReferenceFields(vtable, srcPtr, dstPtr);
        }

        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected void CopyStructWithSlowBarrier(Object srcObj,
                                                 Object dstObj,
                                                 VTable vtable,
                                                 UIntPtr srcOff,
                                                 UIntPtr dstOff)
        {
            slowCopyFieldsVisitor.VisitReferenceFields(vtable,
                                                       srcObj, dstObj,
                                                       srcOff, dstOff);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected void CloneNoBarrier(Object srcObject,
                                      Object dstObject)
        {
            UIntPtr objectSize = System.GCs.ObjectLayout.Sizeof(srcObject);
            int preHeaderSize = PreHeader.Size;
            int postHeaderSize = PostHeader.Size;
            // We don't copy any of the header fields.
            Util.MemCopy(Magic.addressOf(dstObject) + postHeaderSize,
                         Magic.addressOf(srcObject) + postHeaderSize,
                         objectSize - preHeaderSize - postHeaderSize);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected void CloneWithBarrier(Object srcObject,
                                        Object dstObject)
        {
            copyFieldsVisitor.VisitReferenceFields(srcObject, dstObject);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        [AssertDevirtualize]
        protected void CloneWithSlowBarrier(Object srcObject,
                                        Object dstObject)
        {
            slowCopyFieldsVisitor.VisitReferenceFields(srcObject, dstObject);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected void ArrayZeroNoBarrier(Array array, int offset,
                                          int length)
        {
            UIntPtr dataPtr = IndexedDataPtr(array);
            int elementSize = array.vtable.arrayElementSize;
            Buffer.ZeroMemory((byte *)dataPtr + offset * elementSize,
                              length * elementSize);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected void ArrayZeroWithBarrier(Array array, int offset,
                                            int length)
        {
            UIntPtr dataPtr = IndexedDataPtr(array);
            int elementSize = array.vtable.arrayElementSize;
            UIntPtr startAddr = dataPtr + offset * elementSize;
            zeroFieldsVisitor.VisitReferenceFields(array.vtable,
                                                   startAddr, length);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected void ArrayZeroWithSlowBarrier(Array array, int offset,
                                                int length)
        {
            slowZeroFieldsVisitor
                .VisitReferenceFields(array,
                                      IndexedElementOffset(array,offset),
                                      length);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected void ArrayCopyNoBarrier(Array srcArray, int srcOffset,
                                          Array dstArray, int dstOffset,
                                          int length)
        {
            UIntPtr srcDataAddr = IndexedDataPtr(srcArray);
            UIntPtr dstDataAddr = IndexedDataPtr(dstArray);
            int elementSize = srcArray.vtable.arrayElementSize;
            VTable.Assert(elementSize ==
                          dstArray.vtable.arrayElementSize);
            Buffer.MoveMemory((byte *) (dstDataAddr + dstOffset * elementSize),
                              (byte *) (srcDataAddr + srcOffset * elementSize),
                              length * elementSize);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected void ArrayCopyWithBarrier(Array srcArray, int srcOffset,
                                            Array dstArray, int dstOffset,
                                            int length)
        {
            UIntPtr srcDataAddr = IndexedDataPtr(srcArray);
            UIntPtr dstDataAddr = IndexedDataPtr(dstArray);
            int elementSize = srcArray.vtable.arrayElementSize;
            VTable.Assert(elementSize == dstArray.vtable.arrayElementSize);
            UIntPtr srcStartAddr = srcDataAddr + srcOffset * elementSize;
            UIntPtr dstStartAddr = dstDataAddr + dstOffset * elementSize;
            copyFieldsVisitor.VisitReferenceFields(srcArray.vtable,
                                                   srcStartAddr,
                                                   dstStartAddr,
                                                   length);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        [AssertDevirtualize]
        [NoStackLinkCheckTrans]
        protected void ArrayCopyWithSlowBarrier(Array srcArray, int srcOffset,
                                                Array dstArray, int dstOffset,
                                                int length)
        {
            VTable.Assert(srcArray.vtable.arrayElementSize
                          == dstArray.vtable.arrayElementSize);
            slowCopyFieldsVisitor
                .VisitReferenceFields(srcArray.vtable,
                                      srcArray,
                                      dstArray,
                                      IndexedElementOffset(srcArray,
                                                           srcOffset),
                                      IndexedElementOffset(dstArray,
                                                           dstOffset),
                                      length);
        }

        ////////////////////// StoreIndirect to pointer ///////////////////
        // this isn't called by the compiler

        [ForceInline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirect(UIntPtr *location,
                                           Object value,
                                           int mask)
        {
            installedBarrier.StoreIndirectImpl(location, value, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirect(float *location,
                                           float value,
                                           int mask)
        {
            installedBarrier.StoreIndirectImpl(location, value, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirect(double *location,
                                           double value,
                                           int mask)
        {
            installedBarrier.StoreIndirectImpl(location, value, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirect(byte *location,
                                           byte value,
                                           int mask)
        {
            installedBarrier.StoreIndirectImpl(location, value, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirect(ushort *location,
                                           ushort value,
                                           int mask)
        {
            installedBarrier.StoreIndirectImpl(location, value, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirect(uint *location,
                                           uint value,
                                           int mask)
        {
            installedBarrier.StoreIndirectImpl(location, value, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirect(ulong *location,
                                           ulong value,
                                           int mask)
        {
            installedBarrier.StoreIndirectImpl(location, value, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirect(UIntPtr *location,
                                           UIntPtr value,
                                           int mask)
        {
            installedBarrier.StoreIndirectImpl(location, value, mask);
        }

        //////////////////// StoreIndirect to ref /////////////////////////

        [RequiredByBartok]
        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirectByRef(ref Object reference,
                                                Object value,
                                                int mask)
        {
            installedBarrier.StoreIndirectImplByRef(ref reference,
                                                    value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirectByRef(ref float reference,
                                                float value,
                                                int mask)
        {
            installedBarrier.StoreIndirectImplByRef(ref reference,
                                                    value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirectByRef(ref double reference,
                                                double value,
                                                int mask)
        {
            installedBarrier.StoreIndirectImplByRef(ref reference,
                                                    value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirectByRef(ref byte reference,
                                                byte value,
                                                int mask)
        {
            installedBarrier.StoreIndirectImplByRef(ref reference,
                                                    value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirectByRef(ref ushort reference,
                                                ushort value,
                                                int mask)
        {
            installedBarrier.StoreIndirectImplByRef(ref reference,
                                                    value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirectByRef(ref uint reference,
                                                uint value,
                                                int mask)
        {
            installedBarrier.StoreIndirectImplByRef(ref reference,
                                                    value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirectByRef(ref ulong reference,
                                                ulong value,
                                                int mask)
        {
            installedBarrier.StoreIndirectImplByRef(ref reference,
                                                    value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreIndirectByRef(ref UIntPtr reference,
                                                UIntPtr value,
                                                int mask)
        {
            installedBarrier.StoreIndirectImplByRef(ref reference,
                                                    value, mask);
        }

        //////////////////// LoadIndirect from ptr /////////////////////////

        [Inline]
        [NoStackLinkCheckTrans]
        internal static Object LoadObjIndirect(UIntPtr *reference,
                                               int mask)
        {
            return installedBarrier.LoadObjIndirectImpl(reference, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static float LoadIndirect(float* reference,
                                           int mask)
        {
            return installedBarrier.LoadIndirectImpl(reference, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static double LoadIndirect(double* reference,
                                            int mask)
        {
            return installedBarrier.LoadIndirectImpl(reference, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static byte LoadIndirect(byte* reference,
                                          int mask)
        {
            return installedBarrier.LoadIndirectImpl(reference, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static ushort LoadIndirect(ushort* reference,
                                            int mask)
        {
            return installedBarrier.LoadIndirectImpl(reference, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static uint LoadIndirect(uint* reference,
                                          int mask)
        {
            return installedBarrier.LoadIndirectImpl(reference, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static ulong LoadIndirect(ulong* reference,
                                           int mask)
        {
            return installedBarrier.LoadIndirectImpl(reference, mask);
        }

        [Inline]
        [NoStackLinkCheckTrans]
        internal static UIntPtr LoadIndirect(UIntPtr* reference,
                                             int mask)
        {
            return installedBarrier.LoadIndirectImpl(reference, mask);
        }

        //////////////////// LoadIndirect from ref /////////////////////////

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static Object LoadIndirectByRef(ref Object reference,
                                                 int mask)
        {
            return installedBarrier.LoadIndirectImplByRef(ref reference, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static float LoadIndirectByRef(ref float reference,
                                                int mask)
        {
            return installedBarrier.LoadIndirectImplByRef(ref reference, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static double LoadIndirectByRef(ref double reference,
                                                 int mask)
        {
            return installedBarrier.LoadIndirectImplByRef(ref reference, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static byte LoadIndirectByRef(ref byte reference,
                                               int mask)
        {
            return installedBarrier.LoadIndirectImplByRef(ref reference, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ushort LoadIndirectByRef(ref ushort reference,
                                                 int mask)
        {
            return installedBarrier.LoadIndirectImplByRef(ref reference, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static uint LoadIndirectByRef(ref uint reference,
                                               int mask)
        {
            return installedBarrier.LoadIndirectImplByRef(ref reference, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ulong LoadIndirectByRef(ref ulong reference,
                                                int mask)
        {
            return installedBarrier.LoadIndirectImplByRef(ref reference, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static UIntPtr LoadIndirectByRef(ref UIntPtr reference,
                                                  int mask)
        {
            return installedBarrier.LoadIndirectImplByRef(ref reference, mask);
        }

        ///////////////////// StoreObjectField /////////////////////////

        [RequiredByBartok]
        [ForceInline]
        [NoStackLinkCheckTrans]
        internal static void StoreObjectField(Object obj,
                                              UIntPtr fieldOffset,
                                              Object value,
                                              int mask)
        {
            installedBarrier.StoreObjectFieldImpl(obj, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreObjectField(Object obj,
                                              UIntPtr fieldOffset,
                                              float value,
                                              int mask)
        {
            installedBarrier.StoreObjectFieldImpl(obj, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreObjectField(Object obj,
                                              UIntPtr fieldOffset,
                                              double value,
                                              int mask)
        {
            installedBarrier.StoreObjectFieldImpl(obj, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreObjectField(Object obj,
                                              UIntPtr fieldOffset,
                                              byte value,
                                              int mask)
        {
            installedBarrier.StoreObjectFieldImpl(obj, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreObjectField(Object obj,
                                              UIntPtr fieldOffset,
                                              ushort value,
                                              int mask)
        {
            installedBarrier.StoreObjectFieldImpl(obj, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreObjectField(Object obj,
                                              UIntPtr fieldOffset,
                                              uint value,
                                              int mask)
        {
            installedBarrier.StoreObjectFieldImpl(obj, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreObjectField(Object obj,
                                              UIntPtr fieldOffset,
                                              ulong value,
                                              int mask)
        {
            installedBarrier.StoreObjectFieldImpl(obj, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreObjectField(Object obj,
                                              UIntPtr fieldOffset,
                                              UIntPtr value,
                                              int mask)
        {
            installedBarrier.StoreObjectFieldImpl(obj, fieldOffset,
                                                  value, mask);
        }

        ///////////////////// LoadObjectField /////////////////////////

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static Object LoadObjObjectField(Object obj,
                                                  UIntPtr fieldOffset,
                                                  int mask)
        {
            return installedBarrier.LoadObjObjectFieldImpl(obj,
                                                           fieldOffset,
                                                           mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static float LoadFloatObjectField(Object obj,
                                                   UIntPtr fieldOffset,
                                                   int mask)
        {
            return installedBarrier.LoadFloatObjectFieldImpl(obj,
                                                             fieldOffset,
                                                             mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static double LoadDoubleObjectField(Object obj,
                                                     UIntPtr fieldOffset,
                                                     int mask)
        {
            return installedBarrier.LoadDoubleObjectFieldImpl(obj,
                                                              fieldOffset,
                                                              mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static byte LoadByteObjectField(Object obj,
                                                 UIntPtr fieldOffset,
                                                 int mask)
        {
            return installedBarrier.LoadByteObjectFieldImpl(obj,
                                                            fieldOffset,
                                                            mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ushort LoadUShortObjectField(Object obj,
                                                     UIntPtr fieldOffset,
                                                     int mask)
        {
            return installedBarrier.LoadUShortObjectFieldImpl(obj,
                                                              fieldOffset,
                                                              mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static uint LoadUIntObjectField(Object obj,
                                                 UIntPtr fieldOffset,
                                                 int mask)
        {
            return installedBarrier.LoadUIntObjectFieldImpl(obj,
                                                            fieldOffset,
                                                            mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ulong LoadULongObjectField(Object obj,
                                                   UIntPtr fieldOffset,
                                                   int mask)
        {
            return installedBarrier.LoadULongObjectFieldImpl(obj,
                                                             fieldOffset,
                                                             mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static UIntPtr LoadUIntPtrObjectField(Object obj,
                                                       UIntPtr fieldOffset,
                                                       int mask)
        {
            return installedBarrier.LoadUIntPtrObjectFieldImpl(obj,
                                                               fieldOffset,
                                                               mask);
        }

        ///////////////////// StoreStructField ////////////////////////
        // what does this mean for CoCo?
        // find base obj pointer.  if there is none then
        // ignore.  if there is then delegate to StoreObjectField

        [RequiredByBartok]
        [ForceInline]
        [NoStackLinkCheckTrans]
        internal static void StoreStructField(UIntPtr structPtr,
                                              UIntPtr fieldOffset,
                                              Object value,
                                              int mask)
        {
            installedBarrier.StoreStructFieldImpl(structPtr, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreStructField(UIntPtr structPtr,
                                              UIntPtr fieldOffset,
                                              float value,
                                              int mask)
        {
            installedBarrier.StoreStructFieldImpl(structPtr, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreStructField(UIntPtr structPtr,
                                              UIntPtr fieldOffset,
                                              double value,
                                              int mask)
        {
            installedBarrier.StoreStructFieldImpl(structPtr, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreStructField(UIntPtr structPtr,
                                              UIntPtr fieldOffset,
                                              byte value,
                                              int mask)
        {
            installedBarrier.StoreStructFieldImpl(structPtr, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreStructField(UIntPtr structPtr,
                                              UIntPtr fieldOffset,
                                              ushort value,
                                              int mask)
        {
            installedBarrier.StoreStructFieldImpl(structPtr, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreStructField(UIntPtr structPtr,
                                              UIntPtr fieldOffset,
                                              uint value,
                                              int mask)
        {
            installedBarrier.StoreStructFieldImpl(structPtr, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreStructField(UIntPtr structPtr,
                                              UIntPtr fieldOffset,
                                              ulong value,
                                              int mask)
        {
            installedBarrier.StoreStructFieldImpl(structPtr, fieldOffset,
                                                  value, mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreStructField(UIntPtr structPtr,
                                              UIntPtr fieldOffset,
                                              UIntPtr value,
                                              int mask)
        {
            installedBarrier.StoreStructFieldImpl(structPtr, fieldOffset,
                                                  value, mask);
        }

        ///////////////////// LoadStructField ////////////////////////

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static Object LoadObjStructField(UIntPtr obj,
                                                  UIntPtr fieldOffset,
                                                  int mask)
        {
            return installedBarrier.LoadObjStructFieldImpl(obj,
                                                           fieldOffset,
                                                           mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static float LoadFloatStructField(UIntPtr obj,
                                                   UIntPtr fieldOffset,
                                                   int mask)
        {
            return installedBarrier.LoadFloatStructFieldImpl(obj,
                                                             fieldOffset,
                                                             mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static double LoadDoubleStructField(UIntPtr obj,
                                                     UIntPtr fieldOffset,
                                                     int mask)
        {
            return installedBarrier.LoadDoubleStructFieldImpl(obj,
                                                              fieldOffset,
                                                              mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static byte LoadByteStructField(UIntPtr obj,
                                                 UIntPtr fieldOffset,
                                                 int mask)
        {
            return installedBarrier.LoadByteStructFieldImpl(obj,
                                                            fieldOffset,
                                                            mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ushort LoadUShortStructField(UIntPtr obj,
                                                     UIntPtr fieldOffset,
                                                     int mask)
        {
            return installedBarrier.LoadUShortStructFieldImpl(obj,
                                                              fieldOffset,
                                                              mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static uint LoadUIntStructField(UIntPtr obj,
                                                 UIntPtr fieldOffset,
                                                 int mask)
        {
            return installedBarrier.LoadUIntStructFieldImpl(obj,
                                                            fieldOffset,
                                                            mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ulong LoadULongStructField(UIntPtr obj,
                                                   UIntPtr fieldOffset,
                                                   int mask)
        {
            return installedBarrier.LoadULongStructFieldImpl(obj,
                                                             fieldOffset,
                                                             mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static UIntPtr LoadUIntPtrStructField(UIntPtr obj,
                                                       UIntPtr fieldOffset,
                                                       int mask)
        {
            return installedBarrier.LoadUIntPtrStructFieldImpl(obj,
                                                               fieldOffset,
                                                               mask);
        }

        ////////////////////// StoreVectorElement ////////////////////

        [RequiredByBartok]
        [ForceInline]
        [NoStackLinkCheckTrans]
        internal static void StoreVectorElement(Array vector,
                                                int index,
                                                int arrayElementSize,
                                                UIntPtr fieldOffset,
                                                Object value,
                                                int mask)
        {
            installedBarrier.StoreVectorElementImpl(vector,
                                                    index,
                                                    arrayElementSize,
                                                    fieldOffset,
                                                    value,
                                                    mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreVectorElement(Array vector,
                                                int index,
                                                int arrayElementSize,
                                                UIntPtr fieldOffset,
                                                float value,
                                                int mask)
        {
            installedBarrier.StoreVectorElementImpl(vector,
                                                    index,
                                                    arrayElementSize,
                                                    fieldOffset,
                                                    value,
                                                    mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreVectorElement(Array vector,
                                                int index,
                                                int arrayElementSize,
                                                UIntPtr fieldOffset,
                                                double value,
                                                int mask)
        {
            installedBarrier.StoreVectorElementImpl(vector,
                                                    index,
                                                    arrayElementSize,
                                                    fieldOffset,
                                                    value,
                                                    mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreVectorElement(Array vector,
                                                int index,
                                                int arrayElementSize,
                                                UIntPtr fieldOffset,
                                                byte value,
                                                int mask)
        {
            installedBarrier.StoreVectorElementImpl(vector,
                                                    index,
                                                    arrayElementSize,
                                                    fieldOffset,
                                                    value,
                                                    mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreVectorElement(Array vector,
                                                int index,
                                                int arrayElementSize,
                                                UIntPtr fieldOffset,
                                                ushort value,
                                                int mask)
        {
            installedBarrier.StoreVectorElementImpl(vector,
                                                    index,
                                                    arrayElementSize,
                                                    fieldOffset,
                                                    value,
                                                    mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreVectorElement(Array vector,
                                                int index,
                                                int arrayElementSize,
                                                UIntPtr fieldOffset,
                                                uint value,
                                                int mask)
        {
            installedBarrier.StoreVectorElementImpl(vector,
                                                    index,
                                                    arrayElementSize,
                                                    fieldOffset,
                                                    value,
                                                    mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreVectorElement(Array vector,
                                                int index,
                                                int arrayElementSize,
                                                UIntPtr fieldOffset,
                                                ulong value,
                                                int mask)
        {
            installedBarrier.StoreVectorElementImpl(vector,
                                                    index,
                                                    arrayElementSize,
                                                    fieldOffset,
                                                    value,
                                                    mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreVectorElement(Array vector,
                                                int index,
                                                int arrayElementSize,
                                                UIntPtr fieldOffset,
                                                UIntPtr value,
                                                int mask)
        {
            installedBarrier.StoreVectorElementImpl(vector,
                                                    index,
                                                    arrayElementSize,
                                                    fieldOffset,
                                                    value,
                                                    mask);
        }

        ////////////////////// LoadVectorElement ////////////////////

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static Object LoadObjVectorElement(Array vector,
                                                    int index,
                                                    int arrayElementSize,
                                                    UIntPtr fieldOffset,
                                                    int mask)
        {
            return installedBarrier.LoadObjVectorElementImpl(vector,
                                                             index,
                                                             arrayElementSize,
                                                             fieldOffset,
                                                             mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static float LoadFloatVectorElement(Array vector,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     int mask)
        {
            return installedBarrier
                .LoadFloatVectorElementImpl(vector,
                                            index,
                                            arrayElementSize,
                                            fieldOffset,
                                            mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static double LoadDoubleVectorElement(Array vector,
                                                       int index,
                                                       int arrayElementSize,
                                                       UIntPtr fieldOffset,
                                                       int mask)
        {
            return installedBarrier
                .LoadDoubleVectorElementImpl(vector,
                                             index,
                                             arrayElementSize,
                                             fieldOffset,
                                             mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static byte LoadByteVectorElement(Array vector,
                                                   int index,
                                                   int arrayElementSize,
                                                   UIntPtr fieldOffset,
                                                   int mask)
        {
            return installedBarrier.LoadByteVectorElementImpl(vector,
                                                              index,
                                                              arrayElementSize,
                                                              fieldOffset,
                                                              mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ushort LoadUShortVectorElement(Array vector,
                                                       int index,
                                                       int arrayElementSize,
                                                       UIntPtr fieldOffset,
                                                       int mask)
        {
            return installedBarrier
                .LoadUShortVectorElementImpl(vector,
                                             index,
                                             arrayElementSize,
                                             fieldOffset,
                                             mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static uint LoadUIntVectorElement(Array vector,
                                                   int index,
                                                   int arrayElementSize,
                                                   UIntPtr fieldOffset,
                                                   int mask)
        {
            return installedBarrier.LoadUIntVectorElementImpl(vector,
                                                              index,
                                                              arrayElementSize,
                                                              fieldOffset,
                                                              mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ulong LoadULongVectorElement(Array vector,
                                                     int index,
                                                     int arrayElementSize,
                                                     UIntPtr fieldOffset,
                                                     int mask)
        {
            return installedBarrier
                .LoadULongVectorElementImpl(vector,
                                            index,
                                            arrayElementSize,
                                            fieldOffset,
                                            mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static UIntPtr LoadUIntPtrVectorElement(Array vector,
                                                         int index,
                                                         int arrayElementSize,
                                                         UIntPtr fieldOffset,
                                                         int mask)
        {
            return installedBarrier
                .LoadUIntPtrVectorElementImpl(vector,
                                              index,
                                              arrayElementSize,
                                              fieldOffset,
                                              mask);
        }

        ///////////////////// StoreArrayElement /////////////////////

        [RequiredByBartok]
        [ForceInline]
        [NoStackLinkCheckTrans]
        internal static void StoreArrayElement(Array array,
                                               int index,
                                               int arrayElementSize,
                                               UIntPtr fieldOffset,
                                               Object value,
                                               int mask)
        {
            installedBarrier.StoreArrayElementImpl(array,
                                                   index,
                                                   arrayElementSize,
                                                   fieldOffset,
                                                   value,
                                                   mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreArrayElement(Array array,
                                               int index,
                                               int arrayElementSize,
                                               UIntPtr fieldOffset,
                                               float value,
                                               int mask)
        {
            installedBarrier.StoreArrayElementImpl(array,
                                                   index,
                                                   arrayElementSize,
                                                   fieldOffset,
                                                   value,
                                                   mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreArrayElement(Array array,
                                               int index,
                                               int arrayElementSize,
                                               UIntPtr fieldOffset,
                                               double value,
                                               int mask)
        {
            installedBarrier.StoreArrayElementImpl(array,
                                                   index,
                                                   arrayElementSize,
                                                   fieldOffset,
                                                   value,
                                                   mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreArrayElement(Array array,
                                               int index,
                                               int arrayElementSize,
                                               UIntPtr fieldOffset,
                                               byte value,
                                               int mask)
        {
            installedBarrier.StoreArrayElementImpl(array,
                                                   index,
                                                   arrayElementSize,
                                                   fieldOffset,
                                                   value,
                                                   mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreArrayElement(Array array,
                                               int index,
                                               int arrayElementSize,
                                               UIntPtr fieldOffset,
                                               ushort value,
                                               int mask)
        {
            installedBarrier.StoreArrayElementImpl(array,
                                                   index,
                                                   arrayElementSize,
                                                   fieldOffset,
                                                   value,
                                                   mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreArrayElement(Array array,
                                               int index,
                                               int arrayElementSize,
                                               UIntPtr fieldOffset,
                                               uint value,
                                               int mask)
        {
            installedBarrier.StoreArrayElementImpl(array,
                                                   index,
                                                   arrayElementSize,
                                                   fieldOffset,
                                                   value,
                                                   mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreArrayElement(Array array,
                                               int index,
                                               int arrayElementSize,
                                               UIntPtr fieldOffset,
                                               ulong value,
                                               int mask)
        {
            installedBarrier.StoreArrayElementImpl(array,
                                                   index,
                                                   arrayElementSize,
                                                   fieldOffset,
                                                   value,
                                                   mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static void StoreArrayElement(Array array,
                                               int index,
                                               int arrayElementSize,
                                               UIntPtr fieldOffset,
                                               UIntPtr value,
                                               int mask)
        {
            installedBarrier.StoreArrayElementImpl(array,
                                                   index,
                                                   arrayElementSize,
                                                   fieldOffset,
                                                   value,
                                                   mask);
        }

        ////////////////////// LoadArrayElement ////////////////////

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static Object LoadObjArrayElement(Array vector,
                                                   int index,
                                                   int arrayElementSize,
                                                   UIntPtr fieldOffset,
                                                   int mask)
        {
            return installedBarrier.LoadObjArrayElementImpl(vector,
                                                            index,
                                                            arrayElementSize,
                                                            fieldOffset,
                                                            mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static float LoadFloatArrayElement(Array vector,
                                                    int index,
                                                    int arrayElementSize,
                                                    UIntPtr fieldOffset,
                                                    int mask)
        {
            return installedBarrier.LoadFloatArrayElementImpl(vector,
                                                              index,
                                                              arrayElementSize,
                                                              fieldOffset,
                                                              mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static double LoadDoubleArrayElement(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      int mask)
        {
            return installedBarrier
                .LoadDoubleArrayElementImpl(vector,
                                            index,
                                            arrayElementSize,
                                            fieldOffset,
                                            mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static byte LoadByteArrayElement(Array vector,
                                                  int index,
                                                  int arrayElementSize,
                                                  UIntPtr fieldOffset,
                                                  int mask)
        {
            return installedBarrier.LoadByteArrayElementImpl(vector,
                                                             index,
                                                             arrayElementSize,
                                                             fieldOffset,
                                                             mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ushort LoadUShortArrayElement(Array vector,
                                                      int index,
                                                      int arrayElementSize,
                                                      UIntPtr fieldOffset,
                                                      int mask)
        {
            return installedBarrier
                .LoadUShortArrayElementImpl(vector,
                                            index,
                                            arrayElementSize,
                                            fieldOffset,
                                            mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static uint LoadUIntArrayElement(Array vector,
                                                  int index,
                                                  int arrayElementSize,
                                                  UIntPtr fieldOffset,
                                                  int mask)
        {
            return installedBarrier.LoadUIntArrayElementImpl(vector,
                                                             index,
                                                             arrayElementSize,
                                                             fieldOffset,
                                                             mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static ulong LoadULongArrayElement(Array vector,
                                                    int index,
                                                    int arrayElementSize,
                                                    UIntPtr fieldOffset,
                                                    int mask)
        {
            return installedBarrier.LoadULongArrayElementImpl(vector,
                                                              index,
                                                              arrayElementSize,
                                                              fieldOffset,
                                                              mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoStackLinkCheckTrans]
        internal static UIntPtr LoadUIntPtrArrayElement(Array vector,
                                                        int index,
                                                        int arrayElementSize,
                                                        UIntPtr fieldOffset,
                                                        int mask)
        {
            return installedBarrier
                .LoadUIntPtrArrayElementImpl(vector,
                                             index,
                                             arrayElementSize,
                                             fieldOffset,
                                             mask);
        }

        //////////////////// StoreStaticField /////////////////////////
        // only support ref wb for now, since nobody needs integral
        // wb on statics

        [RequiredByBartok]
        [ForceInline]
        [NoStackLinkCheckTrans]
        internal static void StoreStaticField(ref Object staticField,
                                              Object value,
                                              int mask)
        {
            installedBarrier.StoreStaticFieldImpl(ref staticField,
                                                  value, mask);
        }

        //////////////////// LoadStaticField /////////////////////////
        // only support ref rb for now, since nobody needs integral
        // rb on statics

        [RequiredByBartok]
        [Inline]
        internal static Object LoadStaticField(ref Object staticField,
                                               int mask)
        {
            return installedBarrier.LoadStaticFieldImpl(ref staticField,
                                                        mask);
        }

        ///////////////////////// Increment/Decrement /////////////////////
        // REVIEW: maybe optimize these.  or not.

        [ForceInline]
        [RequiredByBartok]
        internal static int AtomicIncrement(ref int reference,
                                            int maskmask)
        {
            for (;;) {
                int oldVal = reference;
                if (Interlocked.CompareExchange(ref reference,
                                                oldVal+1,
                                                oldVal)
                    == oldVal) {
                    return oldVal+1;
                }
            }
        }

        [ForceInline]
        [RequiredByBartok]
        internal static int AtomicDecrement(ref int reference,
                                            int mask)
        {
            for (;;) {
                int oldVal = reference;
                if (Interlocked.CompareExchange(ref reference,
                                                oldVal-1,
                                                oldVal)
                    == oldVal) {
                    return oldVal-1;
                }
            }
        }

        /////////////////////////// AtomicSwap /////////////

        [RequiredByBartok]
        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static Object AtomicSwap(ref Object reference,
                                          Object value,
                                          int mask)
        {
            return installedBarrier.AtomicSwapImpl(ref reference,
                                                   value,
                                                   mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static int AtomicSwap(ref int reference,
                                       int value,
                                       int mask)
        {
            return installedBarrier.AtomicSwapImpl(ref reference,
                                                   value,
                                                   mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static UIntPtr AtomicSwap(ref UIntPtr reference,
                                           UIntPtr value,
                                           int mask)
        {
            return installedBarrier.AtomicSwapImpl(ref reference,
                                                   value,
                                                   mask);
        }

        //////////////// AtomicCompareAndSwap /////////////////

        [RequiredByBartok]
        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static Object AtomicCompareAndSwap(ref Object reference,
                                                    Object newValue,
                                                    Object comparand,
                                                    int mask)
        {
            return
                installedBarrier.AtomicCompareAndSwapImpl(ref reference,
                                                          newValue,
                                                          comparand,
                                                          mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static int AtomicCompareAndSwap(ref int reference,
                                                 int newValue,
                                                 int comparand,
                                                 int mask)
        {
            return
                installedBarrier.AtomicCompareAndSwapImpl(ref reference,
                                                          newValue,
                                                          comparand,
                                                          mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static long AtomicCompareAndSwap(ref long reference,
                                                  long newValue,
                                                  long comparand,
                                                  int mask)
        {
            return
                installedBarrier.AtomicCompareAndSwapImpl(ref reference,
                                                          newValue,
                                                          comparand,
                                                          mask);
        }

        [RequiredByBartok]
        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static UIntPtr AtomicCompareAndSwap(ref UIntPtr reference,
                                                     UIntPtr newValue,
                                                     UIntPtr comparand,
                                                     int mask)
        {
            return
                installedBarrier.AtomicCompareAndSwapImpl(ref reference,
                                                          newValue,
                                                          comparand,
                                                          mask);
        }

        /////////////////////// Forward ////////////////////////

        [RequiredByBartok]
        [ForceInline]
        internal static Object Forward(Object o,int mask)
        {
            return installedBarrier.ForwardImpl(o,mask);
        }

        /////////////////////// MemmoryBarrier ///////////////////////////

        [RequiredByBartok]
        [ForceInline]
        internal static void MemoryBarrier(int mask)
        {
            installedBarrier.MemoryBarrierImpl(mask);
        }

        //////////////////////// Pin ///////////////////////////
        //
        // takes an address at which you wish to pin and returns to
        // you a suitable "pinned" address to use.  may also cause
        // you to wait for any arbitrary amount of time.  but the
        // invariants are:
        // -> the address returned is pinned until the next safepoint,
        //    or until no pinned locals refer to it, whichever comes
        //    later.
        // -> even though the address returned may be different from
        //    the address given, and even though non-pinned pointers
        //    to the object may use totally different addresses, you're
        //    guaranteed that the address returned is the "true"
        //    address of the object, and any modifications made to it
        //    will be seen by anyone else accessing the same object, even
        //    if they do it via a different address.
        [RequiredByBartok]
        [ForceInline]
        internal static UIntPtr Pin(UIntPtr address,
                                    int mask)
        {
            return installedBarrier.PinImpl(address, mask);
        }

        ////////////////////////// Initialize Object /////////////////

        [Inline]
        internal static void InitObject(Object o,VTable vtable)
        {
            installedBarrier.InitObjectImpl(o,vtable);
        }

        // TODO: Eliminate this hack when possible.  That should be either
        // when the compiler is smart enough to devirtualize the
        // installedBarrier.InitObjectImpl call in Barrier.InitObject when
        // doing sepcomp, or when we stop using a class hierarchy of barriers.
        //
        // This method is called only from BootstrapMemory and is required
        // when the compiler cannot statically resolve which barrier to
        // use and the installedBarrier field has not been initialized.
        internal static void BootstrapInitObject(Object o, VTable vtable)
        {
            switch (GC.wbType) {
#if !SINGULARITY || MARK_SWEEP_COLLECTOR || NULL_COLLECTOR
              case WBType.noWB: {
                  EmptyWriteBarrier.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
#endif
#if !SINGULARITY || SEMISPACE_COLLECTOR || SLIDING_COLLECTOR || ADAPTIVE_COPYING_COLLECTOR
              case WBType.Generational: {
                  GenerationalWriteBarrier.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
#endif
#if !SINGULARITY || CONCURRENT_MS_COLLECTOR
              case WBType.CMS: {
                  WriteBarrierCMS.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
#endif
#if !SINGULARITY || ATOMIC_RC_COLLECTOR
              case WBType.ARC: {
                  AtomicRCWriteBarrier.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
#endif
#if !SINGULARITY || SEMISPACE_COLLECTOR || SLIDING_COLLECTOR || ADAPTIVE_COPYING_COLLECTOR
              case WBType.AllCards: {
                  AllCardsWriteBarrier.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
#endif
#if !SINGULARITY
              case WBType.ExpandingCoCo: {
                  ExpandingCoCoBarrier.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
              case WBType.ProbabilisticCoCo: {
                  ProbabilisticCoCoBarrier.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
              case WBType.AbortingCoCo: {
                  AbortingCoCoBarrier.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
              case WBType.BrooksTest: {
                  BrooksBarrierTest.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
              case WBType.BrooksCMSTest: {
                  BrooksCMSBarrierTest.BootstrapInitObjectImpl(o, vtable);
                  break;
              }
#endif
              default: {
                  VTable.NotReached("Unknown write barrier type: "+GC.wbType);
                  break;
              }
            }
        }

        //////////////////////// Weak Ref ////////////////////////////

        [Inline]
        internal static Object WeakRefRead(UIntPtr addr,
                                           int mask)
        {
            return installedBarrier.WeakRefReadImpl(addr, mask);
        }

        [Inline]
        internal static UIntPtr WeakRefWrite(Object obj,
                                             int mask)
        {
            return installedBarrier.WeakRefWriteImpl(obj, mask);
        }

        ///////////////////////// Equality Barriers ///////////////////

        [RequiredByBartok]
        [Inline]
        internal static bool Eq(Object a, Object b, int mask)
        {
            return installedBarrier.EqImpl(a, b, mask);
        }

        [RequiredByBartok]
        [Inline]
        internal static bool Neq(Object a, Object b, int mask)
        {
            return !Eq(a, b, mask);
        }

        ////////////////////////// fast path selection ////////////////

        [RequiredByBartok]
        [ForceInline]
        internal static bool AllowFastPath()
        {
            return installedBarrier.AllowFastPathImpl();
        }

        /////////////////////// CopyStruct ////////////////////////////

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void CopyStruct(Object srcObj,
                                        Object dstObj,
                                        VTable vtable,
                                        UIntPtr srcPtr,
                                        UIntPtr dstPtr)
        {
            installedBarrier.CopyStructImpl(srcObj, dstObj,
                                            vtable, srcPtr, dstPtr);
        }

        //////////////////////////// Clone /////////////////////////////

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void Clone(Object srcObject, Object dstObject)
        {
            installedBarrier.CloneImpl(srcObject, dstObject);
        }

        //////////////////////// ArrayZero //////////////////////////////

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void ArrayZero(Array array, int offset, int length)
        {
            installedBarrier.ArrayZeroImpl(array, offset, length);
        }

        ////////////////////////// ArrayCopy ////////////////////////////

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void ArrayCopy(Array srcArray, int srcOffset,
                                       Array dstArray, int dstOffset,
                                       int length)
        {
            installedBarrier.ArrayCopyImpl(srcArray, srcOffset,
                                           dstArray, dstOffset,
                                           length);
        }

        ////////////////////// Write ////////////////////////////

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void Write(UIntPtr *location, Object value, int mask)
        {
            installedBarrier.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void Write(float *location, float value, int mask)
        {
            installedBarrier.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void Write(double *location, double value, int mask)
        {
            installedBarrier.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void Write(byte *location, byte value, int mask)
        {
            installedBarrier.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void Write(ushort *location, ushort value, int mask)
        {
            installedBarrier.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void Write(uint *location, uint value, int mask)
        {
            installedBarrier.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void Write(ulong *location, ulong value, int mask)
        {
            installedBarrier.WriteImpl(location, value, mask);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        internal static void Write(UIntPtr *location, UIntPtr value, int mask)
        {
            installedBarrier.WriteImpl(location, value, mask);
        }

        ///////////////////////// Visitors... /////////////////////////////

        private class CopyFieldsVisitor : OffsetReferenceVisitor
        {

            // Struct copy
            internal void VisitReferenceFields(VTable vtable,
                                               UIntPtr srcPtr,
                                               UIntPtr dstPtr)
            {
                int postHeaderSize = PostHeader.Size;
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable,
                                         srcPtr - postHeaderSize,
                                         dstPtr - postHeaderSize,
                                         (UIntPtr) postHeaderSize);
                VisitReferenceFieldsTemplate(ref objDesc);
                int preHeaderSize = PreHeader.Size;
                UIntPtr limitSize =
                    ObjectLayout.ObjectSize(vtable) - preHeaderSize;
                UIntPtr previouslyDone = objDesc.extra;
                UIntPtr tailSize = limitSize - previouslyDone;
                if (tailSize > UIntPtr.Zero) {
                    Util.MemCopy(objDesc.secondBase + previouslyDone,
                                 objDesc.objectBase + previouslyDone,
                                 tailSize);
                }
            }

            internal void VisitReferenceFields(Object srcObject,
                                               Object dstObject)
            {
                int postHeaderSize = PostHeader.Size;
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(srcObject.vtable,
                                         Magic.addressOf(srcObject),
                                         Magic.addressOf(dstObject),
                                         (UIntPtr) postHeaderSize);
                UIntPtr objectSize = VisitReferenceFieldsTemplate(ref objDesc);
                int preHeaderSize = PreHeader.Size;
                UIntPtr limitSize = objectSize - preHeaderSize;
                UIntPtr previouslyDone = objDesc.extra;
                UIntPtr tailSize = limitSize - previouslyDone;
                if (tailSize > UIntPtr.Zero) {
                    Util.MemCopy(objDesc.secondBase + previouslyDone,
                                 objDesc.objectBase + previouslyDone,
                                 tailSize);
                }
            }

            // Partial array copy
            internal void VisitReferenceFields(VTable vtable,
                                               UIntPtr srcElementPtr,
                                               UIntPtr dstElementPtr,
                                               int length)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, srcElementPtr, dstElementPtr);
                VisitReferenceFieldsTemplate(ref objDesc, length);
                UIntPtr dataSize =
                    srcElementPtr + length * vtable.arrayElementSize;
                UIntPtr srcLimitAddr = Util.UIntPtrPad(dataSize);
                UIntPtr previouslyDone = objDesc.objectBase + objDesc.extra;
                UIntPtr tailSize = srcLimitAddr - previouslyDone;
                if (tailSize > UIntPtr.Zero) {
                    Util.MemCopy(objDesc.secondBase + objDesc.extra,
                                 previouslyDone, tailSize);
                }
            }

            internal override void FieldOffset(UIntPtr offset,
                                               ref ObjectDescriptor objDesc)
            {
                UIntPtr previouslyDone = objDesc.extra;
                objDesc.extra = offset + UIntPtr.Size;
                UIntPtr norefSize = offset - previouslyDone;
                if (norefSize > UIntPtr.Zero) {
                    Util.MemCopy(objDesc.secondBase + previouslyDone,
                                 objDesc.objectBase + previouslyDone,
                                 norefSize);
                }
                UIntPtr *srcAddr = (UIntPtr *) (objDesc.objectBase + offset);
                UIntPtr *dstAddr = (UIntPtr *) (objDesc.secondBase + offset);
                Object fieldValue = installedBarrier.ReadObjImpl(srcAddr, 0);
                fieldValue =
                    installedBarrier.ForwardImpl(fieldValue,
                                                 BarrierMask.Forward.Nullable);
                installedBarrier.WriteImpl(dstAddr, fieldValue, 0);
            }

        }

        private class SlowCopyFieldsVisitor : OffsetReferenceVisitor
        {

            // Struct copy
            internal void VisitReferenceFields(VTable vtable,
                                               Object src,
                                               Object dst,
                                               UIntPtr srcOff,
                                               UIntPtr dstOff)
            {
                int postHeaderSize = PostHeader.Size;
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable,
                                         Magic.addressOf(src)
                                         + srcOff - postHeaderSize,
                                         Magic.addressOf(dst)
                                         + dstOff - postHeaderSize,
                                         (UIntPtr) postHeaderSize,
                                         src,dst);
                VisitReferenceFieldsTemplate(ref objDesc);
                int preHeaderSize = PreHeader.Size;
                UIntPtr limitSize =
                    ObjectLayout.ObjectSize(vtable) - preHeaderSize;
                UIntPtr previouslyDone = objDesc.extra;
                UIntPtr tailSize = limitSize - previouslyDone;
                MemCopyBarrierSlow(dst,
                                   objDesc.secondBase
                                   + previouslyDone
                                   - Magic.addressOf(dst),
                                   src,
                                   objDesc.objectBase
                                   + previouslyDone
                                   - Magic.addressOf(src),
                                   tailSize);
            }

            // Partial array copy
            internal void VisitReferenceFields(VTable vtable,
                                               Object srcArr,
                                               Object dstArr,
                                               UIntPtr srcOff,
                                               UIntPtr dstOff,
                                               int length)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable,
                                         Magic.addressOf(srcArr) + srcOff,
                                         Magic.addressOf(dstArr) + dstOff,
                                         UIntPtr.Zero,
                                         srcArr, dstArr);
                VisitReferenceFieldsTemplate(ref objDesc, length);
                UIntPtr srcLimitAddr =
                    Magic.addressOf(srcArr) + srcOff
                    + length * vtable.arrayElementSize;
                UIntPtr previouslyDone = objDesc.objectBase + objDesc.extra;
                UIntPtr tailSize = srcLimitAddr - previouslyDone;
                MemCopyBarrierSlow(dstArr,
                                   objDesc.secondBase + objDesc.extra
                                   - Magic.addressOf(dstArr),
                                   srcArr,
                                   previouslyDone - Magic.addressOf(srcArr),
                                   tailSize);
            }

            internal void VisitReferenceFields(Object srcObject,
                                               Object dstObject)
            {
                int postHeaderSize = PostHeader.Size;
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(srcObject.vtable,
                                         Magic.addressOf(srcObject),
                                         Magic.addressOf(dstObject),
                                         (UIntPtr) postHeaderSize,
                                         srcObject,
                                         dstObject);
                UIntPtr objectSize = VisitReferenceFieldsTemplate(ref objDesc);
                int preHeaderSize = PreHeader.Size;
                UIntPtr limitSize = objectSize - preHeaderSize;
                UIntPtr previouslyDone = objDesc.extra;
                UIntPtr tailSize = limitSize - previouslyDone;
                MemCopyBarrierSlow(dstObject,previouslyDone,
                                   srcObject,previouslyDone,
                                   tailSize);
            }

            internal override void FieldOffset(UIntPtr offset,
                                               ref ObjectDescriptor objDesc)
            {
                UIntPtr previouslyDone = objDesc.extra;
                objDesc.extra = offset + UIntPtr.Size;
                UIntPtr norefSize = offset - previouslyDone;
                MemCopyBarrierSlow(objDesc.realSecondBase,
                                   previouslyDone + objDesc.secondBase
                                   - Magic.addressOf(objDesc.realSecondBase),
                                   objDesc.realObjectBase,
                                   previouslyDone + objDesc.objectBase
                                   - Magic.addressOf(objDesc.realObjectBase),
                                   norefSize);
                Object fieldValue =
                    installedBarrier
                    .ReadObjImpl(objDesc.realObjectBase,
                                 offset + objDesc.objectBase
                                 - Magic.addressOf(objDesc.realObjectBase),
                                 0);
                installedBarrier
                    .WriteImpl(objDesc.realSecondBase,
                               offset + objDesc.secondBase
                               - Magic.addressOf(objDesc.realSecondBase),
                               fieldValue,
                               0);
            }

        }

        private class ZeroFieldsVisitor : OffsetReferenceVisitor
        {

            internal void VisitReferenceFields(VTable vtable,
                                               UIntPtr elementAddr,
                                               int length)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, elementAddr);
                VisitReferenceFieldsTemplate(ref objDesc, length);
                UIntPtr limitAddr =
                    elementAddr + length * vtable.arrayElementSize;
                UIntPtr previouslyDone = objDesc.objectBase + objDesc.extra;
                UIntPtr tailSize = limitAddr - previouslyDone;
                if (tailSize > UIntPtr.Zero) {
                    Buffer.ZeroMemory((byte *) previouslyDone, tailSize);
                }
            }

            internal override void FieldOffset(UIntPtr offset,
                                               ref ObjectDescriptor objDesc)
            {
                UIntPtr previouslyDone = objDesc.extra;
                objDesc.extra = offset + UIntPtr.Size;
                UIntPtr norefSize = offset - previouslyDone;
                if (norefSize > UIntPtr.Zero) {
                    Util.MemClear(objDesc.objectBase + previouslyDone,
                                  norefSize);
                }
                UIntPtr *fieldAddr = (UIntPtr *) (objDesc.objectBase + offset);
                installedBarrier.WriteImpl(fieldAddr, null, 0);
            }

        }

        private class SlowZeroFieldsVisitor : OffsetReferenceVisitor
        {

            internal void VisitReferenceFields(Object arr,
                                               UIntPtr off,
                                               int length)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(arr.vtable,
                                         Magic.addressOf(arr) + off,
                                         off,
                                         UIntPtr.Zero,
                                         arr,
                                         null);
                VisitReferenceFieldsTemplate(ref objDesc, length);
                UIntPtr limitAddr =
                    Magic.addressOf(arr) + off + length * arr.vtable.arrayElementSize;
                UIntPtr previouslyDone = objDesc.objectBase + objDesc.extra;
                UIntPtr tailSize = limitAddr - previouslyDone;
                Barrier.MemZeroBarrierSlow(arr,
                                           previouslyDone - Magic.addressOf(arr),
                                           tailSize);
            }

            internal override void FieldOffset(UIntPtr offset,
                                               ref ObjectDescriptor objDesc)
            {
                UIntPtr previouslyDone = objDesc.extra;
                objDesc.extra = offset + UIntPtr.Size;
                UIntPtr norefSize = offset - previouslyDone;
                Barrier
                    .MemZeroBarrierSlow(objDesc.realObjectBase,
                                        objDesc.secondBase + previouslyDone,
                                        norefSize);
                installedBarrier
                    .WriteImpl(objDesc.realObjectBase,
                               objDesc.secondBase + offset,
                               null,
                               0);
            }

        }

    }

}

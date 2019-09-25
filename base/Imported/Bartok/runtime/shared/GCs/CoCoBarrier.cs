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

    using MarkingPhase = CMSMarking.MarkingPhase;

    internal unsafe abstract class CoCoBarrier: Barrier {

        // hook-ins to the system.  maybe this could be redone so that
        // it is more orthogonal.

        internal bool BigEndian {
            get { return false; /* BUGBUG */ }
        }

        [NoBarriers]
        internal static new void Initialize()
        {
            // preWriteFieldsVisitor = new PreWriteFieldsVisitor();
            LowAbortCoCoBarrier.preWriteFieldsVisitor = (PreWriteFieldsVisitor)
                BootstrapMemory.Allocate(typeof(PreWriteFieldsVisitor));
        }

        internal static UIntPtr GCFieldOffset;
        internal static UIntPtr vtableFieldOffset;

        private static MarkingPhase CurrentMarkingPhase {
            [NoStackLinkCheck]
            get { return CMSMarking.CurrentMarkingPhase; }
        }

        // wrappers - used for profiling
        internal static UIntPtr CAS(UIntPtr *loc,
                                    UIntPtr newValue,
                                    UIntPtr comparand)
        {
            UIntPtr result=
                Interlocked.CompareExchange(loc, newValue, comparand);
            if (fProfileCAS && result != comparand) {
                numCASFailed++;
            }
            return result;
        }

        [NoBarriers]
        internal static UIntPtr CAS(ref UIntPtr loc,
                                    UIntPtr newValue,
                                    UIntPtr comparand)
        {
            UIntPtr result=
                Interlocked.CompareExchange(ref loc, newValue, comparand);
            if (fProfileCAS && result != comparand) {
                numCASFailed++;
            }
            return result;
        }

        [NoBarriers]
        internal static int CAS(ref int loc,
                                int newValue,
                                int comparand)
        {
            int result=
                Interlocked.CompareExchange(ref loc, newValue, comparand);
            if (fProfileCAS && result != comparand) {
                numCASFailed++;
            }
            return result;
        }

        internal static int CAS(int *loc,
                                int newValue,
                                int comparand)
        {
            int result=
                Interlocked.CompareExchange(loc, newValue, comparand);
            if (fProfileCAS && result != comparand) {
                numCASFailed++;
            }
            return result;
        }

        internal static long CAS(long *loc,
                                 long newValue,
                                 long comparand)
        {
            long result=Interlocked.CompareExchange(loc, newValue, comparand);
            if (fProfileCAS && result != comparand) {
                numCASFailed++;
            }
            return result;
        }

        [NoBarriers]
        internal static Object CAS(ref Object loc,
                                   Object newValue,
                                   Object comparand)
        {
            Object result =
                Interlocked.CompareExchange(ref loc, newValue, comparand);
            if (fProfileCAS && result != comparand) {
                numCASFailed++;
            }
            return result;
        }

        // hacks

        [NoInline]
        internal static float IntToFloatBits(uint x) {
            return *(float*)Magic.toPointer(ref x);
        }

        [NoInline]
        internal static double LongToDoubleBits(ulong x) {
            return *(double*)Magic.toPointer(ref x);
        }

        [NoInline]
        internal static uint FloatToIntBits(float x) {
            return *(uint*)Magic.toPointer(ref x);
        }

        [NoInline]
        internal static ulong DoubleToLongBits(double x) {
            return *(ulong*)Magic.toPointer(ref x);
        }

        internal enum Phase {
            Idle    = 0,
            Prep    = 1,
            Copy    = 2,
            Fixup   = 3
        }

        internal static Phase phase;
        internal static bool forwarding;
        internal static bool pinning;

        // these force thingies are for profiling
        internal static bool forceSlow;
        internal static bool forceNotIdle;
        internal static bool forceForwarding;
        internal static bool forcePinning;

        internal static bool isNotIdle;

        // The value of this variable is
        //    !((phase == Phase.Idle && !forwarding && !pinning) && !forceSlow)
        // The purposes of this variable is to take advantage of the default
        // initialization of boolean variables to false.  In this case, this
        // allows us to use the fast-path version upon startup.
        private static bool dontAllowFastPath;

        internal static bool allowFastPath {
            get { return !dontAllowFastPath; }
            set { dontAllowFastPath = !value; }
        }

        [MixinConditional("CoCo")]
        [MixinConditional("AllThreadMixins")]
        [Mixin(typeof(Thread))]
        public sealed class CoCoThread : Object {
            internal bool readyForCoCo;
            internal int acknowledgedPhase;
            internal bool acknowledgedForwarding;
            internal bool acknowledgedPinning;
            internal bool pinnedOut;
            internal ulong phaseVersion; // useful for detecting transitions
        }

        internal static CoCoThread MixinThread(Thread t) {
            return (CoCoThread) (Object) t;
        }

        internal static ulong CurThreadPhaseVersion
        {
            get {
                if (Thread.CanGetCurThread) {
                    return MixinThread(Thread.CurrentThread).phaseVersion;
                } else {
                    return 0;
                }
            }
        }

        internal static bool inited;
        internal static Object interlock;

        // NOTE: this code uses ForceInline instead of Inline to indicate that
        // inlining should occur even if the caller is huge.  In general, this
        // attribute should be used with great care.  DO NOT USE IT ELSEWHERE IN
        // THE RUNTIME UNLESS YOU ARE WILLING TO DOCUMENT YOUR USE IN
        // IrSimpleInliner.cs AND Attributes.cs!  AND NEVER USE IT IN
        // APPLICATION OR OS CODE!

        internal static bool NeedsTargetBarrier
        {
            [ForceInline]
            get {
                return CurrentMarkingPhase >= MarkingPhase.ComputingRoots;
            }
        }

        internal static bool NeedsSourceBarrier
        {
            [ForceInline]
            get {
                return CurrentMarkingPhase == MarkingPhase.ComputingRoots;
            }
        }

        internal static bool NeedsTargetOrSourceBarrier
        {
            [ForceInline]
            get {
                return CurrentMarkingPhase >= MarkingPhase.ComputingRoots;
            }
        }

        [AssertDevirtualize]
        internal abstract bool IsInToSpace(UIntPtr ptr);

        internal static void Mark(UIntPtr ptr)
        {
            if (CMSMarking.MarkIfNecessary(ptr) &&
                fVerifyToSpaceMark &&
                ptr!=UIntPtr.Zero &&
                !instance.IsInToSpace(ptr)) {
                VTable.DebugBreak();
            }
        }

        internal static void TargetBarrierWithForward(UIntPtr value)
        {
            if (NeedsTargetBarrier) {
                Mark(ToSpaceAsPtr(value));
            }
        }

        internal static void TargetBarrierNoForward(UIntPtr value)
        {
            if (NeedsTargetBarrier) {
                Mark(value);
            }
        }

        // source barrier needs forwarding during the fixup phase, where
        // the stacks will have from-space references but we want the collector
        // to mark to-space references.
        internal static void SourceBarrierWithForward(UIntPtr value)
        {
            if (NeedsSourceBarrier) {
                Mark(ToSpaceAsPtr(value));
            }
        }

        internal static void SourceBarrierNoForward(UIntPtr value)
        {
            if (NeedsSourceBarrier) {
                Mark(value);
            }
        }

        [NoInline]
        [CalledRarely]
        internal static void
        TargetAndSourceBarrierNoForwardSlow(UIntPtr *target,
                                            UIntPtr source)
        {
            Mark(*target);
            if (NeedsSourceBarrier) {
                Mark(source);
            }
        }

        [ForceInline]
        internal static void TargetAndSourceBarrierNoForward(UIntPtr *target,
                                                             UIntPtr source)
        {
            if (NeedsTargetOrSourceBarrier) {
                TargetAndSourceBarrierNoForwardSlow(target, source);
            }
        }

        [CalledRarely]
        internal static void
        TargetWithForwardAndSourceNoForwardBarrierSlow(UIntPtr *target,
                                                       UIntPtr source)
        {
            Mark(ToSpaceAsPtr(*target));
            if (NeedsSourceBarrier) {
                Mark(source);
            }
        }

        [ForceInline]
        internal static void
        TargetWithForwardAndSourceNoForwardBarrier(UIntPtr *target,
                                                   UIntPtr source)
        {
            if (NeedsTargetOrSourceBarrier) {
                TargetWithForwardAndSourceNoForwardBarrierSlow(target, source);
            }
        }

        [CalledRarely]
        [NoBarriers]
        internal static void
        TargetWithForwardAndSourceNoForwardBarrierSlow(ref Object target,
                                                       Object source)
        {
            Mark(ToSpaceAsPtr(target));
            if (NeedsSourceBarrier) {
                Mark(Magic.addressOf(source));
            }
        }

        [ForceInline]
        internal static void
        TargetWithForwardAndSourceNoForwardBarrier(ref Object target,
                                                   Object source)
        {
            if (NeedsTargetOrSourceBarrier) {
                TargetWithForwardAndSourceNoForwardBarrierSlow(ref target,
                                                               source);
            }
        }

        internal static UIntPtr CoCoWordOffset;

        internal static bool IgnoreOffset(UIntPtr offset)
        {
            return !inited
                || offset == GCFieldOffset
                || offset == vtableFieldOffset
                || offset == CoCoWordOffset;
        }

        // for this object, does this offset represent an internally used, directly
        // accessed (without barriers) immutable entity?
        internal static bool InternalImmutableOffset(Object o,
                                                     UIntPtr offset)
        {
            if (o is Array) {
                return (offset - vtableFieldOffset) <
                    (UIntPtr)(o.vtable.baseLength - PreHeader.Size);
            } else {
                return offset == vtableFieldOffset;
            }
        }

        internal abstract void InitLateStub();

        // call when the heap is inited
        internal static void InitLate()
        {
            if (fDebug) {
                VTable.DebugPrint("CoCo: in InitLate\n");
            }
            interlock=new Object();
            MultiUseWord.GetMonitor(interlock);
            MixinThread(Thread.CurrentThread).readyForCoCo=true;

            // REVIEW: this is just offensive
            GCFieldOffset =
                (UIntPtr)Magic.toPointer(ref ThreadHeaderQueue.MixinObject(instance).preHeader.link)
                - Magic.addressOf(instance);
            vtableFieldOffset =
                (UIntPtr)instance.VTableFieldAddr
                - Magic.addressOf(instance);
            instance.InitLateStub();

            inited=true;
        }

        internal static void ForceSlow()
        {
            VTable.DebugPrint("using FORCE SLOW\n");
            allowFastPath = false;
            forceSlow = true;
        }

        internal static void ForceNotIdle()
        {
            VTable.DebugPrint("using FORCE NOT IDLE\n");
            isNotIdle = true;
            forceNotIdle = true;
        }

        internal static void ForceForwarding()
        {
            VTable.DebugPrint("using FORCE FORWARDING\n");
            forwarding = true;
            forceForwarding = true;
        }

        internal static void ForcePinning()
        {
            VTable.DebugPrint("using FORCE PINNING\n");
            pinning = true;
            forcePinning = true;
        }

        internal static Thread debugThread;

        internal static bool DebugThread
        {
            get {
                if (Thread.CanGetCurThread) {
                    if (debugThread==null) {
                        debugThread=Thread.CurrentThread;
                    }
                    return debugThread==Thread.CurrentThread;
                } else {
                    return true;
                }
            }
        }

        private static UIntPtr interlockAddr, forwardedInterlockAddr;

        internal static void ClientHandshake() {
            if (inited) {
                if (fVerbose) {
                    VTable.DebugPrint("         !! ClientHandshake: interlock at ");
                    VTable.DebugPrint((ulong)Magic.addressOf(interlock));
                    VTable.DebugPrint("\n");
                }
                if (fVerbose) {
                    if (Magic.addressOf(interlock)!=interlockAddr) {
                        VTable.DebugPrint("          !! ClientHandshake seeing interlock at new address: ");
                        VTable.DebugPrint((ulong)Magic.addressOf(interlock));
                        VTable.DebugPrint("\n");
                    }
                    if (ToSpaceAsPtr(interlock)!=forwardedInterlockAddr) {
                        VTable.DebugPrint("          !! ClientHandshake seeing interlock at new FORWARDED address: ");
                        VTable.DebugPrint((ulong)ToSpaceAsPtr(interlock));
                        VTable.DebugPrint("\n");
                    }
                }
                lock (interlock) {
                    if (fVerbose) {
                        interlockAddr=Magic.addressOf(interlock);
                        forwardedInterlockAddr=ToSpaceAsPtr(interlock);
                    }
                    CoCoThread t=MixinThread(Thread.CurrentThread);
                    if (phase!=(Phase)t.acknowledgedPhase ||
                        forwarding!=t.acknowledgedForwarding ||
                        pinning!=t.acknowledgedPinning) {
                        if (fDebug) {
                            VTable.DebugPrint("          !! thread ");
                            VTable.DebugPrint((ulong)Magic.addressOf(t));
                            VTable.DebugPrint(" doing ack\n");
                        }
                        t.acknowledgedPhase=(int)phase;
                        t.acknowledgedForwarding=forwarding;
                        t.acknowledgedPinning=pinning;
                        t.phaseVersion++;
                        Monitor.PulseAll(interlock);
                    }
                }
            }
        }

        internal static bool ExchangeReadyForCoCo(bool value)
        {
            CoCoThread t=MixinThread(Thread.CurrentThread);
            bool result=t.readyForCoCo;
            t.readyForCoCo=value;
            return result;
        }

        internal static void ThreadStart(Thread t_)
        {
            if (inited) {
                lock (interlock) {
                    CoCoThread t = MixinThread(t_);
                    t.readyForCoCo=true;
                    t.acknowledgedPhase=(int)phase;
                    t.acknowledgedForwarding=forwarding;
                    t.acknowledgedPinning=pinning;
                }
            }
        }

        // must have some manner of handshake after this
        internal static void EnablePinning()
        {
            if (fDebug) {
                VTable.DebugPrint("    --> CoCo enabling pinning ");
            }
            pinning = true;
            SetAllowFastPath();
        }

        internal static void SetAllowFastPath()
        {
            allowFastPath =
                (phase == Phase.Idle && !forwarding && !pinning)
                && !forceSlow;
        }

        internal static void ChangePhase(Phase phase_,
                                         bool forwarding_,
                                         bool pinning_)
        {
            if (fDebug) {
                VTable.DebugPrint("    --> CoCo going to ");
                switch (phase_) {
                case Phase.Idle: VTable.DebugPrint("Idle"); break;
                case Phase.Prep: VTable.DebugPrint("Prep"); break;
                case Phase.Copy: VTable.DebugPrint("Copy"); break;
                case Phase.Fixup: VTable.DebugPrint("Fixup"); break;
                default: VTable.NotReached(); break;
                }
                VTable.DebugPrint(" (with");
                if (!forwarding_) {
                    VTable.DebugPrint("out");
                }
                VTable.DebugPrint(" forwarding, with");
                if (!pinning_) {
                    VTable.DebugPrint("out");
                }
                VTable.DebugPrint(" pinning)\n");
            }
            lock (interlock) {
                phase = phase_;
                forwarding = forwarding_ || forceForwarding;
                pinning = pinning_ || forcePinning;
                SetAllowFastPath();
                isNotIdle = phase != Phase.Idle || forceNotIdle;
                CoCoThread t = MixinThread(Thread.CurrentThread);
                t.acknowledgedPhase=(int)phase;
                t.acknowledgedForwarding=forwarding;
                t.acknowledgedPinning=pinning;
                t.phaseVersion++;
                Monitor.PulseAll(interlock);
                for (;;) {
                    bool needToWait=false;
                    bool doPulseAll=false;
                    for (int i = 0; i < Thread.threadTable.Length; ++i) {
                        Thread t_=Thread.threadTable[i];
                        if (t_==null) {
                            continue;
                        }
                        t = MixinThread(t_);
                        if (Transitions.InDormantState(i) ||
                            !t.readyForCoCo ||
                            t.pinnedOut) {
                            t.acknowledgedPhase = (int)phase;
                            t.acknowledgedForwarding = forwarding;
                            t.acknowledgedPinning = pinning;
                        }
                        if (t.pinnedOut && phase==Phase.Idle) {
                            t.pinnedOut=false;
                            doPulseAll=true;
                        }
                        if ((Phase)t.acknowledgedPhase != phase ||
                            t.acknowledgedForwarding != forwarding ||
                            t.acknowledgedPinning != pinning) {
                            if (fDebug) {
                                VTable.DebugPrint("         !! thread ");
                                VTable.DebugPrint((ulong)Magic.addressOf(t));
                                VTable.DebugPrint(" not ack\n");
                            }
                            needToWait = true;
                        }
                    }
                    if (doPulseAll) {
                        Monitor.PulseAll(interlock);
                    }
                    if (!needToWait) {
                        break;
                    }
                    // REVIEW: make the timeout less than 500 ms
                    Monitor.Wait(interlock, 500);
                }
            }
        }

        internal static bool IsIdle
        {
            [ForceInline]
            get {
                return !isNotIdle;
            }
        }

        // Given a pointer to an object or into the PostHeader or payload
        // parts of an object, return the address of the object.
        internal static UIntPtr FindObjectForInteriorPtr(UIntPtr addr)
        {
            UIntPtr result;
            if (SegregatedFreeList.IsGcPtr(addr)) {
                result = GC.installedGC.FindObjectAddr(addr);
            } else {
                result = UIntPtr.Zero;
            }
            return result;
        }

        // Given a pointer to an object or into the PreHeader, PostHeader,
        // or payload parts, return the address of the object.  A pointer
        // past the last element of an object or array, which is considered
        // a valid "user-level" interior pointer into the object, may be
        // considered an interior pointer into the subsequent object in
        // memory, so this method is only to be used to translate from
        // real field addresses to object addresses.
        internal static UIntPtr FindObjectForPreInteriorPtr(UIntPtr addr)
        {
            return FindObjectForInteriorPtr(addr + PreHeader.Size);
        }

        [ForceInline]
        internal static bool StrictlyAllowFastPath(int mask)
        {
            return (mask & BarrierMask.PathSpec.AllowFast)!=0;
        }

        [ForceInline]
        internal static bool AllowIdleFastPath(int mask)
        {
            if ((mask & BarrierMask.PathSpec.UseMask)!=0) {
                return (mask & BarrierMask.PathSpec.AllowFast)!=0;
            } else {
                return IsIdle;
            }
        }

        [ForceInline]
        internal static bool AllowFastPath(int mask)
        {
            if ((mask & BarrierMask.PathSpec.UseMask)!=0) {
                return (mask & BarrierMask.PathSpec.AllowFast)!=0;
            } else {
                return allowFastPath;
            }
        }

        [ForceInline]
        internal static bool AllowPinFastPath(int mask)
        {
            if ((mask & BarrierMask.PathSpec.UseMask)!=0) {
                return (mask & BarrierMask.PathSpec.AllowFast)!=0;
            } else {
                return !pinning;
            }
        }

        [NoBarriers]
        [TrustedNonNull]
        internal static CoCoBarrier instance;

        internal CoCoBarrier()
        {
        }

        [ForceInline]
        protected override bool AllowFastPathImpl()
        {
            return allowFastPath;
        }

        internal abstract bool ObjectIsNotCopied(Object o);

        internal abstract UIntPtr ToSpaceImplBeforeReadyNonNull(Object o);

        internal enum Pinner {
            StackScan,
            Barrier
        }

        [AssertDevirtualize]
        internal abstract UIntPtr DoPin(UIntPtr address,
                                        Pinner pinner);

        [Inline]
        [NoBarriers]
        internal static UIntPtr ToSpaceBeforeReadyImpl(Object o)
        {
            if (o==null) {
                return UIntPtr.Zero;
            } else {
                return instance.ToSpaceImplBeforeReadyNonNull(o);
            }
        }

        [AssertDevirtualize]
        internal abstract UIntPtr ToSpaceImplNonNull(Object o);

        [Inline]
        [NoBarriers]
        internal static UIntPtr ToSpaceImpl(Object o)
        {
            if (o==null) {
                return UIntPtr.Zero;
            } else {
                return instance.ToSpaceImplNonNull(o);
            }
        }

        [NoInline]
        [NoBarriers]
        [CalledRarely]
        internal static UIntPtr ToSpaceImplNoInline(Object o)
        {
            return ToSpaceImpl(o);
        }

        [Inline]
        internal static UIntPtr ToSpaceAsPtr(Object o)
        {
            return ToSpaceImpl(o);
        }

        [Inline]
        internal static UIntPtr ToSpaceAsPtr(UIntPtr addr)
        {
            return ToSpaceImpl(Magic.fromAddress(addr));
        }

        [Inline]
        internal static Object ToSpaceAsObj(Object o)
        {
            return Magic.fromAddress(ToSpaceImpl(o));
        }

        [Inline]
        internal static Object ToSpaceAsObj(UIntPtr addr)
        {
            return Magic.fromAddress(ToSpaceImpl(Magic.fromAddress(addr)));
        }

        [Inline]
        protected override Object WeakRefReadImpl(UIntPtr addr,
                                                  int mask)
        {
            addr=ToSpaceAsPtr(addr);
            if (NeedsTargetBarrier) {
                Mark(addr);
            }
            return Magic.fromAddress(addr);
        }

        [Inline]
        protected override UIntPtr WeakRefWriteImpl(Object obj,
                                                    int mask)
        {
            return ToSpaceAsPtr(obj);
        }

        // returns true if any objects have been tagged for copying.
        internal abstract bool AnyTaggedForCopying
        {
            get;
        }

        // collector calls this method to indicate the intent to copy a given
        // object.  the to-space copy must already be allocated.  no calls to
        // this method are allowed after the pin stack scan.  return false
        // if tagging failed.  spaceOverhead will hold the amount of space
        // overhead induced by tagging (or failing to tag), not counting the
        // to-space.
        internal abstract bool TagObjectForCopy(Object from,
                                                Object to,
                                                out UIntPtr spaceOverhead);

        internal abstract void PinningEnabledHook();

        // returns true if the prep phase is needed.  (if false then go directly
        // to copy.)
        internal abstract bool NeedsPrepPhase {
            get;
        }

        // returns true if any offset pointers (i.e. managed pointers into
        // objects) should result in pinning of the base object.
        internal abstract bool PinOffsetPointers {
            get;
        }

        // collector calls this method to request copying.  can only be called
        // from the copy phase.  returns number of objects actually copied.
        internal abstract ulong Copy();

        // this is _just_ a notification - it doesn't pin the object, it's just
        // what we do if an object ends up being pinned.
        internal static void NotifyPin(UIntPtr objAddr)
        {
            UIntPtr page=PageTable.Page(objAddr);
            if (PageTable.Type(page)!=SegregatedFreeList.SMALL_OBJ_PAGE) {
                return;
            }
            SegregatedFreeList.PageHeader *ph=
                (SegregatedFreeList.PageHeader*)PageTable.PageAddr(page);
            CoCoPageUserValue v=new CoCoPageUserValue(ph->userValue);
            if (v.Marked) {
                v.Pinned=true;
            }
            ph->userValue=v.Bits;
        }

        internal static bool ShouldPin(UIntPtr objAddr)
        {
            UIntPtr page=PageTable.Page(objAddr);
            if (PageTable.Type(page)!=SegregatedFreeList.SMALL_OBJ_PAGE) {
                // in practice this won't be reached
                return true;
            }
            SegregatedFreeList.PageHeader *ph=
                (SegregatedFreeList.PageHeader*)PageTable.PageAddr(page);
            return new CoCoPageUserValue(ph->userValue).Pinned;
        }

        //////////////////// Pre write barriers ////////////////////
        // REVIEW: this isn't general enough.  Currently it is
        // only used by CoCo, but it is probably of use to other
        // collectors.
        //
        // value = the old value at a location being overwritten
        [AssertDevirtualize]
        [ForceInline]
        protected virtual void TargetBarrierImpl(UIntPtr value)
        {
            Mark(value);
        }

        [TrustedNonNull]
        private static PreWriteFieldsVisitor preWriteFieldsVisitor;

        [Inline]
        [AssertDevirtualize]
        protected void PreWriteStruct(VTable vtable,
                                      UIntPtr dstPtr)
        {
            preWriteFieldsVisitor.VisitReferenceFields(vtable, dstPtr);
        }

        [Inline]
        [AssertDevirtualize]
        protected void PreWriteObject(Object dstObject)
        {
            preWriteFieldsVisitor.VisitReferenceFields(dstObject);
        }

        [Inline]
        [AssertDevirtualize]
        protected void PreWriteArray(Array array, int offset,
                                     int length)
        {
            preWriteFieldsVisitor
                .VisitReferenceFields(array.vtable,
                                      Magic.addressOf(array)
                                      + IndexedElementOffset(array, offset),
                                      length);
        }

        private class PreWriteFieldsVisitor : OffsetReferenceVisitor
        {

            // Pre struct copy
            internal void VisitReferenceFields(VTable vtable,
                                               UIntPtr dstPtr)
            {
                int postHeaderSize = PostHeader.Size;
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable,
                                         dstPtr - postHeaderSize);
                VisitReferenceFieldsTemplate(ref objDesc);
            }

            // Pre object copy (already provided)
            //internal void VisitReferenceFields(Object dstObject)

            // Partial array copy or array zero
            internal void VisitReferenceFields(VTable vtable,
                                               UIntPtr dstElementPtr,
                                               int length)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, dstElementPtr);
                VisitReferenceFieldsTemplate(ref objDesc, length);
            }

            internal override void FieldOffset(UIntPtr offset,
                                               ref ObjectDescriptor objDesc)
            {
                UIntPtr *dstAddr = (UIntPtr *) (objDesc.objectBase + offset);
                ((LowAbortCoCoBarrier) Barrier.installedBarrier).TargetBarrierImpl(*dstAddr);
            }

        }

        internal static bool fCount { get { return true; } }
        internal static ulong numPins;
        internal static ulong numWaitPins;
        internal static ulong numPinWaits;
        internal static ulong numAtomics;
        internal static ulong numSlowCopyStructs;
        internal static ulong numSlowClones;
        internal static ulong numSlowArrayZeroes;
        internal static ulong numSlowArrayCopies;
        internal static ulong numTaintPins;

        internal static bool fProfileCAS { get { return true; } }
        internal static ulong numCASFailed;

        internal static void PrintStat(string name, ulong n)
        {
            VTable.DebugPrint(name);
            VTable.DebugPrint(" = ");
            VTable.DebugPrint(n);
            VTable.DebugPrint("\n");
        }

        internal static void PrintStats()
        {
            if (fCount) {
                PrintStat("numPins", numPins);
                PrintStat("numWaitPins", numWaitPins);
                PrintStat("numPinWaits", numPinWaits);
                PrintStat("numAtomics", numAtomics);
                PrintStat("numSlowCopyStructs", numSlowCopyStructs);
                PrintStat("numSlowClones", numSlowClones);
                PrintStat("numSlowArrayZeroes", numSlowArrayZeroes);
                PrintStat("numSlowArrayCopies", numSlowArrayCopies);
            }
            if (fProfileCAS) {
                PrintStat("numCASFailed", numCASFailed);
            }
        }

        internal static bool fDebug        { get { return false; } }
        internal static bool fVerboseNull  { get { return false; } }
        internal static bool fVerboseCopy  { get { return false; } }
        internal static bool fGorierCopy   { get { return false; } }
        internal static bool fVerboseRead  { get { return false; } }
        internal static bool fVerbose      { get { return false; } }
        internal static bool fDebugFindObj { get { return false; } }

        internal static bool fVerifyToSpaceMark { get { return true; } }
    }
}


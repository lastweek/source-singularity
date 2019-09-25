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

    internal unsafe class AbortingCoCoBarrier: CoCoBarrier {
        
        [MixinConditional("AbortingCoCo")]
        [Mixin(typeof(PreHeader))]
        internal struct CoCoPreHeader {
            internal MultiUseWord muw;
            [SelfPoint]
            [NoBarriers]
            internal UIntPtr CoCoWord;
        }
        
        [MixinConditional("AbortingCoCo")]
        [Mixin(typeof(Object))]
        internal class CoCoObject: System.Object {
            internal new CoCoPreHeader preHeader;
        }
        
        internal static CoCoObject MixinObject(Object o) {
            return (CoCoObject)o;
        }
        
        internal static Thread mainThread;
        
        internal override void InitLateStub()
        {
            CoCoWordOffset =
                (UIntPtr)Magic.toPointer(ref MixinObject(interlock).preHeader.CoCoWord)
                - Magic.addressOf(interlock);
            
            mainThread = Thread.CurrentThread;
        }
        
        internal AbortingCoCoBarrier()
        {
        }
        
        internal static new AbortingCoCoBarrier instance;
        
        [NoBarriers]
        internal static new void Initialize()
        {
            CoCoBarrier.instance = AbortingCoCoBarrier.instance =
                (AbortingCoCoBarrier)
                BootstrapMemory.Allocate(typeof(AbortingCoCoBarrier));
        }

        /////////////////////////// forwarding word states
        
        // the CoCoWord contains the forwarding pointer, plus one bit:
        //
        // Copying:
        // This is the lowest-order bit.  If it is zero, then the object is
        // not currently being copied.  This is the default state.  If it
        // is one, it means that copying activity is on-going with this
        // object as the source.  To write to the object, the copying bit
        // must first be cleared by the mutator.
        //
        // If the object gets forwarded (i.e. the forwarding pointer is not
        // a self-pointer), the copying bit gets locked in with
        // a value of 0 (indicating not-copying).  Note
        // that it is illegal to set the copying bit to 1
        // if the forwarding pointer is not a self-pointer.
        
        [ForceInline]
        internal static UIntPtr ForwardPtr(UIntPtr CoCoWord)
        {
            return CoCoWord&~(UIntPtr)3;
        }
        
        [ForceInline]
        internal static bool IsCopying(UIntPtr CoCoWord)
        {
            return (CoCoWord&(UIntPtr)1) != 0;
        }
        
        [ForceInline]
        [NoBarriers]
        internal static bool IsForwarded(UIntPtr CoCoWord,
                                         Object o)
        {
            return ForwardPtr(CoCoWord) != Magic.addressOf(o);
        }
        
        [ForceInline]
        internal static UIntPtr WithForwardPtr(UIntPtr CoCoWord,
                                               UIntPtr forward)
        {
            return (CoCoWord&(UIntPtr)1)|forward;
        }
        
        [ForceInline]
        internal static UIntPtr WithForward(UIntPtr forward)
        {
            return forward;
        }
        
        [ForceInline]
        [NoBarriers]
        internal static UIntPtr WithNoForward(Object o,
                                              bool copying)
        {
            return WithCopying(Magic.addressOf(o),copying);
        }
        
        [ForceInline]
        internal static UIntPtr WithNoForwardCopying(Object o)
        {
            return WithNoForward(o,true);
        }
        
        [ForceInline]
        internal static UIntPtr WithNoForwardNotCopying(Object o)
        {
            return WithNoForward(o,false);
        }
        
        [ForceInline]
        internal static UIntPtr WithCopying(UIntPtr CoCoWord,
                                            bool copying)
        {
            if (copying) {
                return CoCoWord|(UIntPtr)1;
            } else {
                return CoCoWord&~(UIntPtr)1;
            }
        }
        
        /////////////////////////// overriding CoCo and Barrier functionality
        
        [NoBarriers]
        internal override bool ObjectIsNotCopied(Object o)
        {
            // BUGBUG: get rid of this method. it is meaninless.
            return true;
        }
        
        [NoBarriers]
        [Inline]
        internal override bool IsInToSpace(UIntPtr ptr)
        {
            Object o = Magic.fromAddress(ptr);
            return !IsForwarded(MixinObject(o).preHeader.CoCoWord,o);
        }
        
        [NoBarriers]
        [Inline]
        internal override UIntPtr ToSpaceImplBeforeReadyNonNull(Object o)
        {
            return ForwardPtr(MixinObject(o).preHeader.CoCoWord);
        }
        
        [ForceInline]
        [NoBarriers]
        protected override void InitObjectImpl(Object o,VTable vtable)
        {
            MyInitObject(o, vtable);
        }

        [ForceInline]
        [NoBarriers]
        internal static new void BootstrapInitObjectImpl(Object o,
                                                         VTable vtable)
        {
            MyInitObject(o, vtable);
        }
        
        [ForceInline]
        [NoBarriers]
        private static void MyInitObject(Object o, VTable vtable)
        {
            MixinObject(o).preHeader.CoCoWord = WithNoForwardNotCopying(o);
            o.vtable = vtable;
        }

        [Inline]
        internal override UIntPtr DoPin(UIntPtr address,
                                        Pinner pinner)
        {
            UIntPtr baseAddr=FindObjectForInteriorPtr(address);
            Object o=Magic.fromAddress(baseAddr);
            UIntPtr offset=address-baseAddr;
            o=Pin(o,pinner);
            return Magic.addressOf(o)+offset;
        }
        
        [NoBarriers]
        [Inline]
        internal override UIntPtr ToSpaceImplNonNull(Object o)
        {
            return ForwardPtr(MixinObject(o).preHeader.CoCoWord);
        }
        
        [ForceInline]
        [NoBarriers]
        protected override Object ForwardImpl(Object o,int mask)
        {
            if ((mask & BarrierMask.Forward.Nullable)!=0 && o == null) {
                return null;
            } else {
                UIntPtr CoCoWord = MixinObject(o).preHeader.CoCoWord;
                if ((mask & BarrierMask.Forward.Writable)!=0 && IsCopying(CoCoWord)) {
                    return ForwardWritableSlow(o);
                } else {
                    return Magic.fromAddress(ForwardPtr(CoCoWord));
                }
            }
        }
        
        [NoInline]
        [CalledRarely]
        internal static Object ForwardWritableSlow(Object o)
        {
            return Pin(o,Pinner.Barrier);
        }
        
        [NoBarriers]
        internal static bool EqImpl(Object a,Object b)
        {
            return a == b
                || (ToSpaceBeforeReadyImpl(a)
                    == ToSpaceBeforeReadyImpl(b));
        }
        
        [NoBarriers]
        [Inline]
        protected override bool EqImpl(Object a,Object b,
                                       int mask)
        {
            return EqImpl(a,b);
        }
        
        [NoBarriers]
        internal static Object Pin(Object o,
                                   Pinner pinner)
        {
            if (fAbortVerboseDebug) {
                VTable.DebugPrint("Aborter: requested pinning on ");
                VTable.DebugPrint((ulong)Magic.addressOf(o));
                VTable.DebugPrint(" in thread ");
                VTable.DebugPrint((ulong)Magic.addressOf(Thread.CurrentThread));
                VTable.DebugPrint(" with pinner = ");
                VTable.DebugPrint((int)pinner);
                VTable.DebugPrint("\n");
            }
            UIntPtr oldCoCoWord=
                CAS(ref MixinObject(o).preHeader.CoCoWord,
                    WithNoForwardNotCopying(o),
                    WithNoForwardCopying(o));
            if (!IsForwarded(oldCoCoWord,o)) {
                // the object is not forwarded - nothing further to do.
                // (we know that it must now be aborted, since if it
                // was, then that couldn't have changed; and if it wasn't,
                // then our CAS would have succeeded.)
                if (fAbortVerboseDebug && IsCopying(oldCoCoWord)) {
                    VTable.DebugPrint("Aborter: aborted copying on ");
                    VTable.DebugPrint((ulong)Magic.addressOf(o));
                    VTable.DebugPrint(" in thread ");
                    VTable.DebugPrint((ulong)Magic.addressOf(Thread.CurrentThread));
                    VTable.DebugPrint("\n");
                }
                if (fBreakOnAbort &&
                    Thread.CurrentThread!=mainThread &&
                    pinner == Pinner.Barrier) {
                    VTable.DebugBreak();
                }
                return o;
            } else {
                VTable.Assert(pinner == Pinner.Barrier,
                              "Encountered a forwarded object in a pin "+
                              "request that did not originate from the "+
                              "barrier");
                if (fAbortVerboseDebug) {
                    VTable.DebugPrint("Aborter: encountered forwarded object "+
                                      "at ");
                    VTable.DebugPrint((ulong)Magic.addressOf(o));
                    VTable.DebugPrint(" in thread ");
                    VTable.DebugPrint((ulong)Magic.addressOf(Thread.CurrentThread));
                    VTable.DebugPrint("\n");
                }
                return Magic.fromAddress(ForwardPtr(oldCoCoWord));
            }
        }
        
        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected override Object AtomicSwapImpl(ref Object reference,
                                                 Object value,
                                                 int mask)
        {
            TargetWithForwardAndSourceNoForwardBarrier(ref reference,value);
            return Interlocked.Exchange(ref reference,value);
        }

        [AssertDevirtualize]
        [ForceInline]
        [NoBarriers]
        protected override Object
        AtomicCompareAndSwapImpl(ref Object reference,
                                 Object newValue,
                                 Object comparand,
                                 int mask)
        {
            TargetWithForwardAndSourceNoForwardBarrier(ref reference,newValue);
            for (;;) {
                Object oldValue = reference;
                Object myNewValue;
                if (EqImpl(oldValue, comparand)) {
                    myNewValue = newValue;
                } else {
                    myNewValue = oldValue;
                }
                if (Interlocked.CompareExchange(ref reference,
                                                myNewValue, oldValue)
                    == oldValue) {
                    return oldValue;
                }
            }
        }

        [ForceInline]
        [NoBarriers]
        protected override void WriteImpl(UIntPtr *location,
                                          Object value,
                                          int mask)
        {
            UIntPtr valueBits=Magic.addressOf(value);
            TargetWithForwardAndSourceNoForwardBarrier(location,valueBits);
            *location=valueBits;
        }
        
        [ForceInline]
        [NoBarriers]
        protected override void WriteImplByRef(ref Object location,
                                               Object value,
                                               int mask)
        {
            TargetWithForwardAndSourceNoForwardBarrier(ref location,value);
            location=value;
        }
        
        class TagNode {
            internal Object from;
            internal Object to;
            internal TagNode next;
        }
        
        static TagNode tagHead;
        static ulong nTagged;
        
        internal override bool AnyTaggedForCopying
        {
            get {
                return tagHead!=null;
            }
        }
        
        internal override bool TagObjectForCopy(Object from,
                                                Object to,
                                                out UIntPtr spaceOverhead)
        {
            TagNode tn=new TagNode();
            spaceOverhead=ObjectLayout.Sizeof(tn);
            tn.next=tagHead;
            tn.from=from;
            tn.to=to;
            tagHead=tn;
            nTagged++;
            return true;
        }
        
        [NoBarriers]
        internal override void PinningEnabledHook()
        {
            if (fAbortDebug) {
                VTable.DebugPrint("Aborter: un-aborting ");
                VTable.DebugPrint(nTagged);
                VTable.DebugPrint(" objects.\n");
            }
            for (TagNode n=tagHead;
                 n!=null;
                 n=n.next) {
                if (fAbortVerboseDebug) {
                    VTable.DebugPrint("Aborter: un-aborting ");
                    VTable.DebugPrint((ulong)Magic.addressOf(n.from));
                    VTable.DebugPrint("\n");
                }
                UIntPtr oldCoCoWord=
                    CAS(ref MixinObject(n.from).preHeader.CoCoWord,
                        WithNoForwardCopying(n.from),
                        WithNoForwardNotCopying(n.from));
                VTable.Assert(!IsCopying(oldCoCoWord));
                VTable.Assert(!IsForwarded(oldCoCoWord,n.from));
            }
            if (fAbortDebug) {
                VTable.DebugPrint("Aborter: un-aborted ");
                VTable.DebugPrint(nTagged);
                VTable.DebugPrint(" objects.\n");
            }
        }

        internal override bool NeedsPrepPhase
        {
            get {
                return false;
            }
        }
        
        internal override bool PinOffsetPointers {
            [Inline]
            get { return true; }
        }
        
        [NoBarriers]
        internal override ulong Copy()
        {
            ulong cnt=0;
            
            TagNode myTagHead=tagHead;
            ulong myNTagged=nTagged;
            tagHead=null;
            nTagged=0;
            
            if (fAbortDebug) {
                VTable.DebugPrint("Aborter: copying ");
                VTable.DebugPrint(myNTagged);
                VTable.DebugPrint(" objects.\n");
            }

            // first do all of the copying
            for (TagNode n=myTagHead;
                 n!=null;
                 n=n.next) {
                Util.MemCopy(Magic.addressOf(n.to)-PreHeader.Size,
                             Magic.addressOf(n.from)-PreHeader.Size,
                             ObjectLayout.Sizeof(n.from));
                // fix the forwarding word in the to-space object (without
                // this it'll point at from-space)
                MixinObject(n.to).preHeader.CoCoWord=WithNoForwardNotCopying(n.to);
            }

            if (fAbortDebug) {
                VTable.DebugPrint("Aborter: copied ");
                VTable.DebugPrint(myNTagged);
                VTable.DebugPrint(" objects.\n");
            }

            // now attempt to forward all objects.
            for (TagNode n=myTagHead;
                 n!=null;
                 n=n.next) {
                UIntPtr oldCoCoWord=
                    CAS(ref MixinObject(n.from).preHeader.CoCoWord,
                        WithForward(Magic.addressOf(n.to)),
                        WithNoForwardCopying(n.from));
                VTable.Assert(!IsForwarded(MixinObject(n.to).preHeader.CoCoWord,
                                           n.to));
                if (oldCoCoWord == WithNoForwardCopying(n.from)) {
                    // copy successful
                    cnt++;
                }
            }
            
            if (fAbortDebug) {
                VTable.DebugPrint("Aborter: forwarded ");
                VTable.DebugPrint(cnt);
                VTable.DebugPrint(" objects.\n");
            }

            return cnt;
        }
        
        private static bool fAbortDebug { get { return false; } }
        private static bool fAbortVerboseDebug { get { return false; } }
        private static bool fBreakOnAbort { get { return false; } }
    }

}


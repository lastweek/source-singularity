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

    internal unsafe class ProbabilisticCoCoBarrier: LowAbortCoCoBarrier {
        internal static new ProbabilisticCoCoBarrier instance;
        
        [NoBarriers]
        internal static new void Initialize()
        {
            if (fDietDebug) {
                VTable.DebugPrint("Diet DoCo!\n");
            }
            
            ProbabilisticCoCoBarrier.instance =
                (ProbabilisticCoCoBarrier)
                BootstrapMemory.Allocate(typeof(ProbabilisticCoCoBarrier));
            ProbabilisticCoCoBarrier.instance.InitEarly();
            LowAbortCoCoBarrier.Initialize();
        }
        
        internal static UIntPtr Alpha {
            get {
                // FIXME: make this random
                return (UIntPtr)0xD1E7C0C0;
            }
        }

        // handling of CoCo word
        
        // four states:
        // - simple
        // - tagged
        // - copying
        // - forwarded
        
        // copying means that the object is tagged and there is the chance
        // that some field's most up-to-date value is in to-space.  copying
        // means that we cannot pin without waiting.
        
        // forwarded means that all fields are copied.
        
        [Inline]
        static internal UIntPtr ForwardPtr(UIntPtr CoCoWord)
        {
            return CoCoWord&~(UIntPtr)3;
        }
        
        [Inline]
        static internal bool IsTagged(UIntPtr CoCoWord)
        {
            return (CoCoWord&(UIntPtr)3) == (UIntPtr)1;
        }

        [Inline]
        static internal bool IsCopying(UIntPtr CoCoWord)
        {
            return (CoCoWord&(UIntPtr)3) == (UIntPtr)2;
        }

        [Inline]
        static internal bool IsForwarded(UIntPtr CoCoWord)
        {
            return (CoCoWord&(UIntPtr)3) == (UIntPtr)3;
        }

        [Inline]
        static internal bool IsSimple(UIntPtr CoCoWord)
        {
            return CoCoWord==UIntPtr.Zero;
        }
        
        [Inline]
        static internal UIntPtr Simple()
        {
            return UIntPtr.Zero;
        }
        
        [Inline]
        static internal UIntPtr Tagged(UIntPtr forward)
        {
            VTable.Assert(ForwardPtr(forward)==forward);
            return forward|(UIntPtr)1;
        }
        
        [Inline]
        static internal UIntPtr Copying(UIntPtr CoCoWord)
        {
            return ForwardPtr(CoCoWord)|(UIntPtr)2;
        }
        
        [Inline]
        static internal UIntPtr Forwarded(UIntPtr CoCoWord)
        {
            return ForwardPtr(CoCoWord)|(UIntPtr)3;
        }
        
        [Inline]
        [NoBarriers]
        internal override UIntPtr ToSpaceImplBeforeReadyNonNull(Object o)
        {
            UIntPtr CoCoWord = MixinObject(o).preHeader.CoCoWord;
            if (IsSimple(CoCoWord)) {
                return Magic.addressOf(o);
            } else {
                return ForwardPtr(CoCoWord);
            }
        }

        [Inline]
        [NoBarriers]
        internal override bool IsInToSpace(UIntPtr ptr)
        {
            return !IsForwarded(MixinObject(Magic.fromAddress(ptr)).preHeader.CoCoWord);
        }
        
        [Inline]
        [NoBarriers]
        internal override UIntPtr ToSpaceImplNonNull(Object o)
        {
            UIntPtr CoCoWord = MixinObject(o).preHeader.CoCoWord;
            if (IsForwarded(CoCoWord)) {
                return ForwardPtr(CoCoWord);
            } else {
                return Magic.addressOf(o);
            }
        }
        
        [Inline]
        [NoBarriers]
        internal static bool CASCoCoWord(Object o,
                                         UIntPtr value,
                                         UIntPtr comparand)
        {
            return CAS(ref MixinObject(o).preHeader.CoCoWord,
                       value,comparand)
                == comparand;
        }
        
        internal static UIntPtr PinDirect(UIntPtr baseAddr,
                                          UIntPtr address,
                                          Pinner pinner)
        {
            Object o = Magic.fromAddress(baseAddr);
            
            UIntPtr CoCoWord;
            
            bool waited=false;
            for (;;) {
                CoCoWord = MixinObject(o).preHeader.CoCoWord;
                if (IsSimple(CoCoWord) || IsForwarded(CoCoWord)) {
                    break;
                } else if (IsCopying(CoCoWord)) {
                    VTable.Assert(pinner==Pinner.Barrier);
                    if (fCount) {
                        if (!waited) {
                            waited=true;
                            numWaitPins++;
                        }
                        numPinWaits++;
                    }
                    // wait until it's copied
                    lock (interlock) {
                        CoCoThread t = MixinThread(Thread.CurrentThread);
                        t.pinnedOut = true;
                        Monitor.PulseAll(interlock);
                        while (t.pinnedOut) {
                            Monitor.Wait(interlock);
                        }
                    }
                    // ok, now try again (by the time we get here the
                    // object could already be in the process of being
                    // copied agagin!)
                } else if (IsTagged(CoCoWord)) {
                    CASCoCoWord(o,Simple(),CoCoWord);
                    NotifyPin(baseAddr);
                }
            }
            
            // what does it mean to get here?  the object cannot
            // be moved until the next pinning safepoint prior to
            // a transition out of Idle.
            
            VTable.Assert(IsSimple(CoCoWord) || IsForwarded(CoCoWord));
            
            // correct address
            if (IsForwarded(CoCoWord)) {
                address -= baseAddr;
                address += ForwardPtr(CoCoWord);
            }
            
            return address;
        }
        
        [NoInline]
        private static UIntPtr PinDirectAndForwardValue(UIntPtr baseAddr,
                                                         UIntPtr address,
                                                         ref Object objValue)
        {
            return PinDirect(baseAddr,address,Pinner.Barrier);
        }
        
        // Worst Hack Ever.  PinDirect may cause an unbounded number of
        // phase changes, meaning that the pointer we're writing into the
        // heap may be "from-spaced" any number of times - causing it to
        // potentially point at rotting garbage.  So, we force the collector
        // to do some forwarding for us.
        [NoInline]
        private static UIntPtr PinDirectAndForwardValue(UIntPtr baseAddr,
                                                         UIntPtr address,
                                                         bool isObject,
                                                         ref UIntPtr shiftedValue)
        {
            Object objValue = null;
            if (isObject) {
                objValue = Magic.fromAddress(shiftedValue);
            }
            address=PinDirectAndForwardValue(baseAddr,address,ref objValue);
            if (isObject) {
                shiftedValue = Magic.addressOf(objValue);
            }
            return address;
        }

        internal override UIntPtr DoPin(UIntPtr address,
                                        Pinner pinner)
        {
            if (fCount) {
                numPins++;
            }

            UIntPtr baseAddr = FindObjectForInteriorPtr(address);
            if (baseAddr != UIntPtr.Zero) {
                address=PinDirect(baseAddr, address, pinner);
            }

            return address;
        }
        
        protected override UIntPtr ReadWordSlow(Object o,
                                                UIntPtr offset)
        {
            UIntPtr word = *(UIntPtr*)(Magic.addressOf(o) + offset);
            if (word == Alpha) {
                UIntPtr CoCoWord = MixinObject(o).preHeader.CoCoWord;
                if (IsSimple(CoCoWord)) {
                    return word;
                } else {
                    return *(UIntPtr*)(ForwardPtr(CoCoWord) + offset);
                }
            } else {
                return word;
            }
        }
        
        static void WriteWordNoForward(UIntPtr *ptr,
                                       UIntPtr offset,
                                       UIntPtr mask,
                                       UIntPtr shiftedValue,
                                       bool isObject)
        {
            if (mask == UIntPtr.MaxValue) {
                if (isObject) {
                    TargetBarrierWithForward(*ptr);
                }
                *ptr = shiftedValue;
            } else {
                for (;;) {
                    UIntPtr oldVal=*ptr;
                    if (CAS(ptr,
                            (oldVal&~mask)|(shiftedValue&mask),
                            oldVal)
                        == oldVal) {
                        return;
                    }
                }
            }
        }
        
        static void WriteWordNoForward(Object o,
                                       UIntPtr offset,
                                       UIntPtr mask,
                                       UIntPtr shiftedValue,
                                       bool isObject)
        {
            UIntPtr *ptr = (UIntPtr*)(Magic.addressOf(o) + offset);
            WriteWordNoForward(ptr, offset, mask, shiftedValue, isObject);
        }
        
        static void WriteWordForwarded(Object o,
                                       UIntPtr offset,
                                       UIntPtr mask,
                                       UIntPtr shiftedValue,
                                       bool isObject)
        {
            WriteWordNoForward(Magic.fromAddress(ForwardPtr(MixinObject(o).preHeader.CoCoWord)),
                               offset, mask, shiftedValue, isObject);
        }
        
        protected override void WriteWordSlow(Object o,
                                              UIntPtr offset,
                                              UIntPtr mask,
                                              UIntPtr shiftedValue,
                                              bool isObject)
        {
            UIntPtr *ptr = (UIntPtr*)(Magic.addressOf(o) + offset);
            for (;;) {
                UIntPtr word = *ptr;
                if (phase == Phase.Idle ||
                    IgnoreOffset(offset)) {
                    WriteWordNoForward(o,offset,mask,shiftedValue,isObject);
                    return;
                } else if (word == Alpha) {
                    UIntPtr CoCoWord = MixinObject(o).preHeader.CoCoWord;
                    if (IsCopying(CoCoWord) ||
                        IsForwarded(CoCoWord) ||
                        (phase == Phase.Copy
                         && IsTagged(CoCoWord)
                         && CASCoCoWord(o,Copying(CoCoWord),CoCoWord))) {
                        // we saw an Alpha, and the object state indicates that
                        // Alphas mean forwarding.  but, we might not get
                        // here if the object was tagged and we failed to flip it to
                        // copying.  that would only happen if someone managed to
                        // pin the object.
                        WriteWordForwarded(o,offset,mask,shiftedValue,isObject);
                        return;
                    } else if (IsSimple(CoCoWord)) {
                        // object was either never tagged or has been pinned by someone
                        // else.
                        WriteWordNoForward(o,offset,mask,shiftedValue,isObject);
                        return;
                    } else if (phase == Phase.Prep
                               && IsTagged(CoCoWord)
                               && CASCoCoWord(o,Simple(),CoCoWord)) {
                        // we pinned the object.
                        numTaintPins++;
                        NotifyPin(Magic.addressOf(o));
                        WriteWordNoForward(o,offset,mask,shiftedValue,isObject);
                        return;
                    }
                } else {
                    UIntPtr newWord = (word&~mask)|(shiftedValue&mask);
                    if (newWord == Alpha) {
                        // FIXME: do stats or debug
                        // FIXME: potentially wrong.  the code does not assume that
                        // a write barrier may change phases.  on the other hand,
                        // if we end up in here then it means that the code was alredy
                        // assuming slow-path, and if we emerge from here, then it means
                        // we had a sync point ... so it should be fine.
                        
                        ptr=(UIntPtr*)PinDirectAndForwardValue(Magic.addressOf(o),
                                                                (UIntPtr)ptr,
                                                                isObject,
                                                                ref shiftedValue);
                        
                        // ok, object is pinned or forwarded; write to the new
                        // location for this field.
                        WriteWordNoForward(ptr, offset, mask, shiftedValue, isObject);
                        return;
                    }
                    // we get here if neither the new or the old word was an Alpha.
                    // this is the common case.
                    if (isObject) {
                        TargetBarrierWithForward(word);
                    }
                    if (CAS(ptr,newWord,word) == word) {
                        return;
                    }
                }
            }
        }

        static bool WeakCASNoForward(UIntPtr *ptr,
                                     UIntPtr offset,
                                     UIntPtr mask,
                                     UIntPtr shiftedValue,
                                     UIntPtr shiftedComparand)
        {
            UIntPtr oldVal=*ptr;
            UIntPtr comparand = (oldVal&~mask)|(shiftedComparand&mask);
            return CAS(ptr,
                       (oldVal&~mask)|(shiftedValue&mask),
                       comparand)
                == comparand;
        }
        
        static bool WeakCASNoForward(Object o,
                                     UIntPtr offset,
                                     UIntPtr mask,
                                     UIntPtr shiftedValue,
                                     UIntPtr shiftedComparand)
        {
            UIntPtr *ptr = (UIntPtr*)(Magic.addressOf(o) + offset);
            return WeakCASNoForward(ptr, offset, mask, shiftedValue, shiftedComparand);
        }
        
        static bool WeakCASForwarded(Object o,
                                     UIntPtr offset,
                                     UIntPtr mask,
                                     UIntPtr shiftedValue,
                                     UIntPtr shiftedComparand)
        {
            return WeakCASNoForward(Magic.fromAddress(ForwardPtr(MixinObject(o).preHeader.CoCoWord)),
                                    offset, mask, shiftedValue, shiftedComparand);
        }
        
        protected override bool WeakCASWordSlow(Object o,
                                                UIntPtr offset,
                                                UIntPtr mask,
                                                UIntPtr shiftedValue,
                                                UIntPtr shiftedComparand,
                                                bool isObject)
        {
            UIntPtr *ptr = (UIntPtr*)(Magic.addressOf(o) + offset);
            UIntPtr word = *ptr;
            if (phase == Phase.Idle ||
                IgnoreOffset(offset)) {
                return WeakCASNoForward(o,offset,mask,shiftedValue,shiftedComparand);
            } else if (word == Alpha) {
                UIntPtr CoCoWord = MixinObject(o).preHeader.CoCoWord;
                if (IsCopying(CoCoWord) ||
                    IsForwarded(CoCoWord) ||
                    (phase == Phase.Copy
                     && IsTagged(CoCoWord)
                     && CASCoCoWord(o,Copying(CoCoWord),CoCoWord))) {
                    // we saw an Alpha, and the object state indicates that
                    // Alphas mean forwarding.  but, we might not get
                    // here if the object was tagged and we failed to flip it to
                    // copying.  that would only happen if someone managed to
                    // pin the object.
                    return WeakCASForwarded(o,offset,mask,shiftedValue,shiftedComparand);
                } else if (IsSimple(CoCoWord)) {
                    // object was either never tagged or has been pinned by someone
                    // else.
                    return WeakCASNoForward(o,offset,mask,shiftedValue,shiftedComparand);
                } else if (phase == Phase.Prep
                           && IsTagged(CoCoWord)
                           && CASCoCoWord(o,Simple(),CoCoWord)) {
                    // we pinned the object.
                    numTaintPins++;
                    NotifyPin(Magic.addressOf(o));
                    return WeakCASNoForward(o,offset,mask,shiftedValue,shiftedComparand);
                }
            } else if ((word&mask) == (shiftedComparand&mask)) {
                UIntPtr newWord = (word&~mask)|(shiftedValue&mask);
                if (newWord == Alpha) {
                    // FIXME: do stats or debug
                    ptr=(UIntPtr*)PinDirectAndForwardValue(Magic.addressOf(o),
                                                           (UIntPtr)ptr,
                                                           isObject,
                                                           ref shiftedValue);
                    // ok, object is pinned or forwarded; write to the new
                    // location for this field.
                    return WeakCASNoForward(ptr, offset, mask, shiftedValue, shiftedComparand);
                }
                return CAS(ptr,newWord,word) == word;
            }
            return false;
        }

        protected override bool WeakCASArbitrarySlow(Object o,
                                                     UIntPtr offset,
                                                     UIntPtr size,
                                                     ulong value,
                                                     ulong comparand) {
            VTable.NotImplemented();
            VTable.DebugBreak();
            return false;
        }
        
        class TagNode {
            internal Object from;
            internal TagNode next;
        }
        
        static TagNode tagHead;
        
        internal override bool AnyTaggedForCopying {
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
            tn.from=from;
            tn.next=tagHead;

            // prepare to-space object
            UIntPtr begin=UIntPtr.Zero-(UIntPtr)PreHeader.Size;
            UIntPtr end=
                ((ObjectLayout.Sizeof(from)+sizeof(UIntPtr)-1)
                 &~((UIntPtr)sizeof(UIntPtr)-1))
                -PreHeader.Size;
            for (UIntPtr offset=begin;
                 offset!=end;
                 offset+=sizeof(UIntPtr)) {
                if (!IgnoreOffset(offset)) {
                    *(UIntPtr*)(Magic.addressOf(to)+offset)=Alpha;
                }
            }
            
            // now we can tag from-space
            if (CASCoCoWord(from,Tagged(Magic.addressOf(to)),Simple())) {
                tagHead=tn;
                return true;
            } else {
                return false;
            }
        }
        
        internal override bool NeedsPrepPhase {
            get {
                return true;
            }
        }
        
        [NoBarriers]
        static bool CopyObject(Object from)
        {
            if (fDietVerboseCopyDebug) {
                VTable.DebugPrint("   Copying ");
                VTable.DebugPrint((ulong)Magic.addressOf(from));
                VTable.DebugPrint(" with CoCoWord = ");
                VTable.DebugPrint((ulong)MixinObject(from).preHeader.CoCoWord);
                VTable.DebugPrint("\n");
            }
            for (;;) {
                UIntPtr CoCoWord=MixinObject(from).preHeader.CoCoWord;
                if (IsSimple(CoCoWord)) {
                    // got pinned .. ignore
                    return false;
                } else if (IsTagged(CoCoWord)) {
                    if (ShouldPin(Magic.addressOf(from))) {
                        if (CASCoCoWord(from,Simple(),CoCoWord)) {
                            // pinned
                            NotifyPin(Magic.addressOf(from));
                            return false;
                        }
                    } else {
                        CASCoCoWord(from,Copying(CoCoWord),CoCoWord);
                    }
                } else if (IsCopying(CoCoWord)) {
                    Object to=Magic.fromAddress(ForwardPtr(CoCoWord));
                    UIntPtr begin=UIntPtr.Zero-(UIntPtr)PreHeader.Size;
                    UIntPtr end=
                        ((ObjectLayout.Sizeof(from)+sizeof(UIntPtr)-1)
                         &~((UIntPtr)sizeof(UIntPtr)-1))
                        -PreHeader.Size;
                    if (fDietVerboseCopyDebug) {
                        VTable.DebugPrint("      copying to ");
                        VTable.DebugPrint((ulong)Magic.addressOf(to));
                        VTable.DebugPrint("; begin = ");
                        VTable.DebugPrint((ulong)begin);
                        VTable.DebugPrint("; end = ");
                        VTable.DebugPrint((ulong)end);
                        VTable.DebugPrint("; PreHeader.Size = ");
                        VTable.DebugPrint((ulong)PreHeader.Size);
                        VTable.DebugPrint("; Sizeof(from) = ");
                        VTable.DebugPrint((ulong)ObjectLayout.Sizeof(from));
                        VTable.DebugPrint("; Sizeof(to) = ");
                        VTable.DebugPrint((ulong)ObjectLayout.Sizeof(to));
                        VTable.DebugPrint("\n");
                    }
                    for (UIntPtr offset=begin;
                         offset!=end;
                         offset+=sizeof(UIntPtr)) {
                        if (!IgnoreOffset(offset)) {
                            UIntPtr *fptr=(UIntPtr*)(Magic.addressOf(from)+offset);
                            UIntPtr *tptr=(UIntPtr*)(Magic.addressOf(to)+offset);
                            for (;;) {
                                UIntPtr word=*fptr;
                                if (word==Alpha) {
                                    // NOTE: this case will only be hit the first time
                                    // around the loop.  if it's not hit the first time
                                    // it'll never get hit.
                                    break;
                                }
                                *tptr=word;
                                if (InternalImmutableOffset(from,offset) ||
                                    CAS(fptr,Alpha,word)==word) {
                                    break;
                                }
                            }
                        }
                    }
                    MixinObject(from).preHeader.CoCoWord=Forwarded(CoCoWord);
                    return true;
                } else {
                    VTable.NotReached();
                }
            }
        }

        [NoBarriers]
        internal override ulong Copy()
        {
            if (fDietDebug) {
                VTable.DebugPrint("Doing Diet CoCo Copy\n");
            }
            
            ulong numCopied=0;
            TagNode tagHead=ProbabilisticCoCoBarrier.tagHead;
            ProbabilisticCoCoBarrier.tagHead=null;
            for (TagNode cur=tagHead;
                 cur!=null;
                 cur=cur.next) {
                if (CopyObject(cur.from)) {
                    numCopied++;
                }
            }
            
            if (fDietDebug) {
                VTable.DebugPrint("Done With Diet CoCo Copy\n");
            }
            
            return numCopied;
        }
        
        private static bool fDietDebug { get { return false; } }
        private static bool fDietVerboseCopyDebug { get { return false; } }
    }
}


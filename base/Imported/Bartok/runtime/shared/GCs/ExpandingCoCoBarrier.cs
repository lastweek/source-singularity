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

    internal unsafe class ExpandingCoCoBarrier: LowAbortCoCoBarrier {

        internal static new ExpandingCoCoBarrier instance;
        
        [NoBarriers]
        internal static new void Initialize()
        {
            ExpandingCoCoBarrier.instance =
                (ExpandingCoCoBarrier)
                BootstrapMemory.Allocate(typeof(ExpandingCoCoBarrier));
            ExpandingCoCoBarrier.instance.InitEarly();
            LowAbortCoCoBarrier.Initialize();
        }
        
        internal enum ObjState {
            SimpleOrForwarded    = 0,
            Tagged               = 1,
            Tainted              = 2,
            Expanded             = 3,
        }
        
        [NoBarriers]
        internal struct ForwardingWord {
            private UIntPtr original;
            private UIntPtr CoCoWord;

            internal ForwardingWord(Object original,
                                    UIntPtr CoCoWord)
            {
                this.original = Magic.addressOf(original);
                this.CoCoWord = CoCoWord;
            }
            
            internal ForwardingWord(UIntPtr original,
                                    UIntPtr CoCoWord)
            {
                this.original = original;
                this.CoCoWord = CoCoWord;
            }
            
            internal ForwardingWord(Object original,
                                    ObjState state,
                                    UIntPtr forward)
            {
                this.original = Magic.addressOf(original);
                this.CoCoWord = ((UIntPtr)(uint)(int)state)|forward;
            }
            
            internal ForwardingWord(Object original,
                                    ObjState state,
                                    Object forward)
            {
                this.original = Magic.addressOf(original);
                this.CoCoWord = ((UIntPtr)(uint)(int)state)|Magic.addressOf(forward);
            }
            
            internal ForwardingWord(UIntPtr original,
                                    ObjState state,
                                    UIntPtr forward)
            {
                this.original = original;
                this.CoCoWord = ((UIntPtr)(uint)(int)state)|forward;
            }
            
            internal bool IsClear
            {
                get {
                    return CoCoWord == UIntPtr.Zero;
                }
            }
            
            internal UIntPtr Bits
            {
                get {
                    return CoCoWord;
                }
            }
            
            // This is messed up.  I don't like it.

            internal UIntPtr ForwardBitsRaw
            {
                get {
                    return CoCoWord&~(UIntPtr)3;
                }
            }
            
            internal UIntPtr ForwardBits
            {
                get {
                    UIntPtr result = UIntPtr.Zero;
                    if (State==ObjState.SimpleOrForwarded) {
                        result = ForwardBitsRaw;
                    }
                    if (result==UIntPtr.Zero) {
                        return original;
                    } else {
                        return result;
                    }
                }
            }
            
            internal Object Forward {
                get { return Magic.fromAddress(ForwardBits); }
            }
            
            internal WideObject Wide
            {
                get {
                    return (WideObject)Magic.fromAddress(ForwardBitsRaw);
                }
            }
            
            internal UIntPtr ForwardInternal(UIntPtr oldPtr)
            {
                return (oldPtr-original)+ForwardBits;
            }
            
            internal ObjState State
            {
                get {
                    return (ObjState)(int)(CoCoWord&3);
                }
            }
            
            internal ForwardingWord WithState(ObjState state)
            {
                return new ForwardingWord(original,
                                          state,
                                          ForwardBitsRaw);
            }
            
            internal ForwardingWord WithForwardBits(UIntPtr forwardBits)
            {
                return new ForwardingWord(original,
                                          State,
                                          forwardBits);
            }
            
            internal ForwardingWord WithForward(Object o)
            {
                return WithForwardBits(Magic.addressOf(o));
            }
            
            internal ForwardingWord WithWide(WideObject w)
            {
                return WithForward(w);
            }
            
            internal ForwardingWord Clear()
            {
                return new ForwardingWord(original,
                                          ObjState.SimpleOrForwarded,
                                          UIntPtr.Zero);
            }
        }
        
        [NoBarriers]
        internal static ForwardingWord GetForwardingWord(Object o)
        {
            UIntPtr word;
            if (fVerbose && DebugThread) {
                VTable.DebugPrint("GetForwardingWord: reading from ");
                VTable.DebugPrint((ulong)Magic.addressOf(o));
                VTable.DebugPrint("\n");
                
                UIntPtr *wordPtr =
                    Magic.toPointer(ref MixinObject(o).preHeader.CoCoWord);

                VTable.DebugPrint("GetForwardingWord: wordPtr = ");
                VTable.DebugPrint((ulong)wordPtr);
                VTable.DebugPrint("\n");

                word = *wordPtr;
                
                VTable.DebugPrint("GetForwardingWord: from ");
                VTable.DebugPrint((ulong)Magic.addressOf(o));
                VTable.DebugPrint(" read ");
                VTable.DebugPrint((ulong)word);
                VTable.DebugPrint("\n");
            } else {
                word = MixinObject(o).preHeader.CoCoWord;
            }
            return new ForwardingWord(o, word);
        }

        [Inline]
        [NoBarriers]
        internal override UIntPtr ToSpaceImplBeforeReadyNonNull(Object o)
        {
            UIntPtr CoCoWord = MixinObject(o).preHeader.CoCoWord;
            UIntPtr ForwardBitsRaw=CoCoWord&~(UIntPtr)(uint)3;
            if (ForwardBitsRaw == 0) {
                return Magic.addressOf(o);
            } else if (((uint)(CoCoWord&3)) == (uint)ObjState.SimpleOrForwarded) {
                return ForwardBitsRaw;
            } else {
                return Magic.addressOf(((WideObject)Magic.fromAddress(ForwardBitsRaw)).copy);
            }
        }

        [Inline]
        [NoBarriers]
        internal override bool IsInToSpace(UIntPtr ptr)
        {
            UIntPtr CoCoWord = MixinObject(Magic.fromAddress(ptr)).preHeader.CoCoWord;
            UIntPtr ForwardBitsRaw=CoCoWord&~(UIntPtr)(uint)3;
            return ForwardBitsRaw == 0
                || ((uint)(CoCoWord&3)) != (uint)ObjState.SimpleOrForwarded;
        }
        
        [Inline]
        [NoBarriers]
        internal override UIntPtr ToSpaceImplNonNull(Object o)
        {
            // this needs some memory barriers.
            UIntPtr CoCoWord = MixinObject(o).preHeader.CoCoWord;
            UIntPtr ForwardBitsRaw=CoCoWord&~(UIntPtr)(uint)3;
            if (ForwardBitsRaw == 0 ||
                ((uint)(CoCoWord&3)) != (uint)ObjState.SimpleOrForwarded) {
                return Magic.addressOf(o);
            } else {
                return ForwardBitsRaw;
            }
        }

        [NoBarriers]
        internal static bool SwapObjectState(Object o,
                                             ForwardingWord value,
                                             ForwardingWord comparand)
        {
            return CAS(ref MixinObject(o).preHeader.CoCoWord,
                       value.Bits,
                       comparand.Bits)
                == comparand.Bits;
        }
        
        [NoBarriers]
        internal static void SetObjectState(Object o,
                                            ForwardingWord f)
        {
            MixinObject(o).preHeader.CoCoWord = f.Bits;
        }
        
        internal enum WordState {
            Original    = 0,
            InWide      = 1,
            InCopy      = 2,
        }
        
        [NoBarriers]
        internal struct WordStatus {
            private UIntPtr word;
            
            internal WordStatus(UIntPtr word)
            {
                this.word = word;
            }
            
            internal WordStatus(WordState state,
                                bool inAction,
                                UIntPtr version)
            {
                word = ((UIntPtr)state)
                     | (UIntPtr)(inAction?4:0)
                     | (version<<3);
            }
            
            internal UIntPtr Word
            {
                get {
                    return word;
                }
            }
            
            internal UIntPtr* asPointer {
                get { return Magic.toPointer(ref word); }
            }
            
            internal WordState State
            {
                get {
                    return (WordState)(int)(word&(UIntPtr)3);
                }
                set {
                    word=((word&~(UIntPtr)3)|((UIntPtr)value));
                }
            }
            
            internal bool InAction {
                get { return (word&4)!=0; }
                set {
                    if (value) word|=(UIntPtr)4;
                    else word&=~(UIntPtr)4;
                }
            }
            
            internal UIntPtr Version {
                get { return word>>3; }
                set { word=(value<<3); }
            }
            
            internal WordStatus WithState(WordState value) {
                WordStatus result=this;
                result.State=value;
                return result;
            }
            
            internal WordStatus WithInAction(bool value) {
                WordStatus result=this;
                result.InAction=value;
                return result;
            }
            
            internal WordStatus WithVersion(UIntPtr value) {
                WordStatus result=this;
                result.Version=value;
                return result;
            }
        }
        
        internal enum ActionResult {
            None         = 0,
            Success      = 1,
            Failure      = 2,
        }
        
        internal struct WordAction {
            internal int index;

            internal WordStatus statusValue;
            internal UIntPtr payloadValue;
            
            internal WordStatus statusComparand;
            internal UIntPtr payloadComparand;
            
            internal WordAction(int index,
                                WordStatus statusValue,
                                UIntPtr payloadValue,
                                WordStatus statusComparand,
                                UIntPtr payloadComparand)
            {
                this.index = index;
                this.statusValue = statusValue;
                this.payloadValue = payloadValue;
                this.statusComparand = statusComparand;
                this.payloadComparand = payloadComparand;
            }
        }

        internal class Action {
            private int res;
            internal WordAction[] words;
            
            internal Action(uint n) {
                res=(int)ActionResult.None;
                words=new WordAction[n];
            }
            
            internal ActionResult Res {
                get { return (ActionResult)res; }
            }
            
            private UIntPtr myVersion {
                get { return Magic.addressOf(this)>>3; }
            }
            
            [NoBarriers]
            private bool setResult(ActionResult newRes) {
                int oldRes=CAS(ref this.res,
                               (int)newRes,
                               (int)ActionResult.None);
                return oldRes == (int)ActionResult.None
                    || oldRes == (int)newRes;
            }
            
            private void rollback(WideObject wide,
                                  uint limit) {
                // NOTE: this completely and truly reverts the status and
                // payload.  No trace is left of this action having ever
                // taken place, not even in the version number.
                for (uint i=0;i<limit;++i) {
                    WordAction wa=words[i];
                    if (wa.statusComparand.State==WordState.Original) {
                        wide.words[wa.index]
                            .CAS(wa.statusComparand,UIntPtr.Zero,
                                 wa.statusComparand
                                 .WithVersion(myVersion).WithInAction(true),
                                 UIntPtr.Zero);
                    } else {
                        wide.words[wa.index]
                            .CAS(wa.statusComparand,
                                 wa.payloadComparand,
                                 wa.statusComparand
                                 .WithVersion(myVersion).WithInAction(true),
                                 wa.payloadComparand);
                    }
                }
            }

            internal void complete(WideObject wide) {
                // prepare version numbers
                for (uint i=0;i<words.Length;++i) {
                    words[i].statusValue.Version=myVersion;
                }
                
                // now proceed with the compare phase
                for (uint i=0;i<words.Length && Res==ActionResult.None;++i) {
                    WordAction wa=words[i];
                    if (wa.statusComparand.State==WordState.Original) {
                        UIntPtr oldVal=*(UIntPtr*)
                            (Magic.addressOf(wide.from) + ToOffset(wa.index));
                        if (oldVal!=wa.payloadComparand) {
                            if (setResult(ActionResult.Failure)) {
                                rollback(wide, i);
                            }
                            return;
                        }
                        WordStatus statusResult;
                        UIntPtr payloadResult; // ignored
                        wide.words[wa.index]
                            .CAS(wa.statusComparand
                                 .WithVersion(myVersion).WithInAction(true),
                                 UIntPtr.Zero,
                                 wa.statusComparand,
                                 UIntPtr.Zero,
                                 out statusResult,
                                 out payloadResult);
                        if (statusResult.Version==myVersion) {
                            // someone is ahead of us.  we know this
                            // because the statusValue.Version is our version.
                        } else if (statusResult.Word
                                   != wa.statusComparand.Word) {
                            // note that we know that if we were expecting
                            // the status to be Original then the only way
                            // for the payload to change is if the status
                            // changes too.
                            
                            // if we get here we know that either the
                            // action had completed a _long_ time ago or
                            // it has genuinely failed.  for this reason
                            // we do everything with a CAS.
                            if (setResult(ActionResult.Failure)) {
                                rollback(wide, i);
                            }
                            return;
                        }
                    } else {
                        WordStatus statusResult;
                        UIntPtr payloadResult;
                        wide.words[wa.index]
                            .CAS(wa.statusComparand
                                 .WithVersion(myVersion).WithInAction(true),
                                 wa.payloadComparand,
                                 wa.statusComparand,wa.payloadComparand,
                                 out statusResult,out payloadResult);
                        if (statusResult.Version==wa.statusValue.Version) {
                            // someone is ahead of us (see discussion above)
                        } else if (statusResult.Word
                                   != wa.statusComparand.Word ||
                                   payloadResult
                                   != wa.payloadComparand) {
                            // if we get here we know that either the
                            // action had completed a _long_ time ago or
                            // it has genuinely failed.  for this reason
                            // we do everything with a CAS.
                            if (setResult(ActionResult.Failure)) {
                                rollback(wide, i);
                            }
                            return;
                        }
                    }
                }

                // We will only get here if the CAS has a genuine right to
                // succeed.  But there are really two possibilities here:
                // -> The CAS really should succeed.
                // -> There is at least one other concurrent attempt to
                //    complete this action.  There was a non-atomic write to
                //    the words that we're writing that occurred after the
                //    other attempt had already concluded failure; this
                //    attempt makes the words appear as if they are correct
                //    for the CAS to succeed.  In this case the CAS can
                //    either succeed or fail - either would be a linearizable
                //    result.  So, we race to be the first to set the CAS
                //    result.

                if (setResult(ActionResult.Success)) {
                    for (uint i=0;i<words.Length && Res==ActionResult.None;++i) {
                        WordAction wa=words[i];
                        if (wa.statusComparand.State==WordState.Original) {
                            wide.words[wa.index]
                                .CAS(wa.statusValue,wa.payloadValue,
                                     wa.statusComparand
                                     .WithVersion(myVersion).WithInAction(true),
                                     UIntPtr.Zero);
                        } else {
                            wide.words[wa.index]
                                .CAS(wa.statusValue,wa.payloadValue,
                                     wa.statusComparand
                                     .WithVersion(myVersion).WithInAction(true),
                                     wa.payloadComparand);
                        }
                    }
                }
            }
        }

        // BUGBUG: in order to allow the collector to run concurrently
        // with the Copy phase, turn this into an object (rather than a
        // struct) and have two subclasses, one for primitives and one
        // for object references.  Create the instances lazily.
        [StructLayout(LayoutKind.Sequential)]
        internal struct WideWord {
            internal WordStatus status;
            internal UIntPtr payload; // may be object pointer!!
            
            internal WideWord(WordStatus status,
                              UIntPtr payload) {
                this.status = status;
                this.payload = payload;
            }
            
            [NoBarriers]
            internal void CAS(WordStatus statusValue,
                              UIntPtr payloadValue,
                              WordStatus statusComparand,
                              UIntPtr payloadComparand,
                              out WordStatus statusResult,
                              out UIntPtr payloadResult) {
                // BUGBUG: rudely assuming little-endian 32-bit architecture
                long result=CoCoBarrier.CAS((long*)status.asPointer,
                                            ((long)statusValue.Word)
                                            |(((long)payloadValue)<<32),
                                            ((long)statusComparand.Word)
                                            |(((long)payloadComparand)<<32));
                long lower32=(((long)1)<<32)-1;
                statusResult=new WordStatus((UIntPtr)(result&lower32));
                payloadResult=(UIntPtr)((result>>32)&lower32);
            }

            [NoBarriers]
            internal bool CAS(WordStatus statusValue,
                              UIntPtr payloadValue,
                              WordStatus statusComparand,
                              UIntPtr payloadComparand) {
                WordStatus statusResult;
                UIntPtr payloadResult;
                CAS(statusValue,payloadValue,
                    statusComparand,payloadComparand,
                    out statusResult,out payloadResult);
                return statusResult.Word==statusComparand.Word
                    && payloadResult==payloadComparand;
            }
            
            [NoBarriers]
            internal void AtomicRead(out WordStatus statusResult,
                                     out UIntPtr payloadResult) {
                // BUGBUG: rudely assuming little-endian 32-bit architecture
                long result=*(long*)status.asPointer;
                long lower32=(((long)1)<<32)-1;
                statusResult=new WordStatus((UIntPtr)(result&lower32));
                payloadResult=(UIntPtr)((result>>32)&lower32);
            }
            
            [NoBarriers]
            internal WideWord AtomicRead() {
                WordStatus statusResult;
                UIntPtr payloadResult;
                AtomicRead(out statusResult,out payloadResult);
                return new WideWord(statusResult,payloadResult);
            }
        }
        
        internal class WideObject {
            internal WideObject next;
            internal Object from;
            internal Object copy;
            internal Object action; /* must be Object not Action because
                                       of CompareExchange! */
            
            internal WideWord[] words;
            
            internal WideObject(WideObject next,
                                Object from,
                                Object copy) {
                this.next=next;
                this.from=from;
                this.copy=copy;
                
                UIntPtr nwords=
                    (ObjectLayout.Sizeof(from)+sizeof(UIntPtr)-1)
                    /(uint)sizeof(UIntPtr);
                
                this.words=new WideWord[(int)nwords];
                
                this.action=null;
            }
            
            internal UIntPtr spaceOverhead {
                get {
                    return ObjectLayout.Sizeof(this)
                        + ObjectLayout.Sizeof(words);
                }
            }
            
            internal void completeOneAction() {
#if !ARM && !ISA_ARM
                // HACK: MemoryBarrier is unimplemented in ARM 
                // and causes compile-time failures when building
                // mscorlib in sepcomp mode. This change will break
                // CoCo if built with ARM.
                Thread.MemoryBarrier();
#endif
                Action a=(Action)this.action;
                if (a!=null) {
                    a.complete(this);
                    CAS(ref this.action,null,a);
                }
            }
        }
        
        internal static int ToIndex(UIntPtr offset)
        {
            return (int)((offset + PreHeader.Size)/(uint)sizeof(UIntPtr));
        }
        
        internal static UIntPtr ToOffset(int index)
        {
            return (UIntPtr)index*(UIntPtr)sizeof(UIntPtr)
                - PreHeader.Size;
        }

        internal override UIntPtr DoPin(UIntPtr address,
                                        Pinner pinner)
        {
            if (fCount) {
                numPins++;
            }

            UIntPtr baseAddr = FindObjectForInteriorPtr(address);
            if (baseAddr != UIntPtr.Zero) {
                Object o = Magic.fromAddress(baseAddr);
                
                ForwardingWord f;
                
                bool waited=false;
                for (;;) {
                    f = GetForwardingWord(o);
                    if (f.State == ObjState.SimpleOrForwarded) {
                        break;
                    } else if (f.State == ObjState.Expanded) {
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
                    } else {
                        SwapObjectState(o,f.Clear(),f);
                        NotifyPin(baseAddr);
                    }
                }
                
                // what does it mean to get here?  the object cannot
                // be moved until the next pinning safepoint prior to
                // a transition out of Idle.

                VTable.Assert(f.State == ObjState.SimpleOrForwarded);

                // correct address
                f = GetForwardingWord(o);
                address -= baseAddr;
                address += f.ForwardBits;
            }

            return address;
        }

        [NoInline]
        [CalledRarely]
        protected override UIntPtr ReadWordSlow(Object o,
                                                UIntPtr offset)
        {
            // FIXME: add debug here!
            ForwardingWord f=GetForwardingWord(o);
            if (fVerbose && DebugThread) {
                VTable.DebugPrint("f.State = ");
                VTable.DebugPrint((int)f.State);
                VTable.DebugPrint(", f.ForwardBits = ");
                VTable.DebugPrint((ulong)f.ForwardBits);
                VTable.DebugPrint("\n");
            }
            UIntPtr result;
            if (IgnoreOffset(offset)) {
                result=*(UIntPtr*)(Magic.addressOf(o) + offset);
            } else if (f.State==ObjState.Expanded) {
                /*
                if (false && phase==Phase.Idle) {
                    VTable.DebugPrint("PROBLEM: found expanded object in idle phase, o = ");
                    VTable.DebugPrint((ulong)Magic.addressOf(o));
                    VTable.DebugPrint("\n");
                    VTable.NotReached();
                }
                */
                if (true && f.Wide.from!=o) {
                    VTable.DebugPrint("PROBLEM: expanded object is corrupt.  object = ");
                    VTable.DebugPrint((ulong)Magic.addressOf(o));
                    VTable.DebugPrint(", forwarding word = ");
                    VTable.DebugPrint((ulong)f.Bits);
                    VTable.DebugPrint(", wide.from = ");
                    VTable.DebugPrint((ulong)Magic.addressOf(f.Wide.from));
                    VTable.DebugPrint(", ToSpace(o) = ");
                    VTable.DebugPrint((ulong)ToSpaceAsPtr(o));
                    VTable.DebugPrint(", ToSpace(wide.from) = ");
                    VTable.DebugPrint((ulong)ToSpaceAsPtr(f.Wide.from));
                    VTable.DebugPrint("\n");
                    VTable.NotReached();
                }
                WideObject wide=f.Wide;
                WideWord ww=wide.words[ToIndex(offset)].AtomicRead();
                WordState s=ww.status.State;
                switch (s) {
                case WordState.Original:
                    result=*(UIntPtr*)(Magic.addressOf(wide.from)+offset);
                    break;
                case WordState.InWide:
                    if (fVerbose) {
                        VTable.DebugPrint("actually reading from wide\n");
                    }
                    result=ww.payload;
                    break;
                case WordState.InCopy:
                    if (fVerbose) {
                        VTable.DebugPrint("actually reading from copy\n");
                    }
                    result=*(UIntPtr*)(Magic.addressOf(wide.copy)+offset);
                    break;
                default:
                    VTable.NotReached();
                    result=UIntPtr.Zero; // make compiler happy
                    break;
                }
            } else {
                result=*(UIntPtr*)(f.ForwardBits + offset);
            }
            if (fVerboseRead) {
                UIntPtr oldRes=*(UIntPtr*)(Magic.addressOf(o)+offset);
                if (result!=oldRes) {
                    VTable.DebugPrint("read from ");
                    VTable.DebugPrint((ulong)Magic.addressOf(o));
                    VTable.DebugPrint("+");
                    VTable.DebugPrint((ulong)offset);
                    VTable.DebugPrint(": result = ");
                    VTable.DebugPrint((ulong)result);
                    VTable.DebugPrint(", oldRes = ");
                    VTable.DebugPrint((ulong)oldRes);
                    VTable.DebugPrint("\n");
                }
            }
            return result;
        }

        internal static void WriteWordNoForward(Object o,
                                                UIntPtr offset,
                                                UIntPtr mask,
                                                UIntPtr shiftedValue,
                                                bool isObject)
        {
            UIntPtr *ptr = (UIntPtr*)(Magic.addressOf(o) + offset);
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
        
        internal static void WriteWordOriginal(ForwardingWord f,
                                               UIntPtr offset,
                                               UIntPtr mask,
                                               UIntPtr shiftedValue,
                                               bool isObject) {
            WriteWordNoForward(f.Forward,offset,mask,shiftedValue,isObject);
        }
        
        internal static bool ExpandIfNecessary(ref ForwardingWord f,
                                               Object o) {
            if (f.State == ObjState.Tagged) {
                // the Object is not yet expanded so attempt to
                // expand it.
                if (fVerbose) {
                    VTable.DebugPrint("  >> Expanding: ");
                    VTable.DebugPrint((ulong)Magic.addressOf(o));
                    VTable.DebugPrint("\n");
                }
                ForwardingWord newf=f.WithState(ObjState.Expanded);
                if (!SwapObjectState(o,newf,f)) {
                    return false;
                }
                f=newf;
            }
            return true;
        }
        
        [NoInline]
        [CalledRarely]
        protected override void WriteWordSlow(Object o,
                                              UIntPtr offset,
                                              UIntPtr mask,
                                              UIntPtr shiftedValue,
                                              bool isObject)
        {
            if (fVerbose && DebugThread) {
                VTable.DebugPrint("Writing slowly to ");
                VTable.DebugPrint((ulong)Magic.addressOf(o));
                VTable.DebugPrint(" + ");
                VTable.DebugPrint((ulong)offset);
                VTable.DebugPrint(" the value ");
                VTable.DebugPrint((ulong)shiftedValue);
                VTable.DebugPrint(" & ");
                VTable.DebugPrint((ulong)mask);
                if (isObject) {
                    VTable.DebugPrint(", which represents an object");
                }
                VTable.DebugPrint(".\n");
            }

            // this is a transaction that keeps retrying until it
            // succeeds.  it is lock-free but not wait-free.  for
            // word-sized fields it could be wait-free if we wanted
            // it to be.  to understand this code, I'd suggest looking
            // for the return statements - these signify the commit
            // points of the transaction.  any time you fall out of the
            // if branches and reloop, this signifies an abort-and-retry.
            // at one point there is also an abort-and-retry performed
            // using a continue statement.
            for (;;) {
                Phase p=phase;
                ForwardingWord f=GetForwardingWord(o);
                if (IgnoreOffset(offset)) {
                    WriteWordNoForward(o,offset,mask,shiftedValue,isObject);
                    return;
                } else if (f.State==ObjState.SimpleOrForwarded ||
                           p==Phase.Idle) {
                    // If we get here it means that one of the following
                    // is going on:
                    // -> The object is in some weird state but we're still
                    //    in the idle phase.
                    // -> The object became Simple at some point after the
                    //    write fast path observed that it was not Simple.
                    //    This could have occurred through the use of
                    //    pinning.
                    // -> The object became Forwarded at some point after
                    //    the write fast path observed that it was not
                    //    Forwarded.  This could have happened because
                    //    copying for this object concluded.
                    
                    WriteWordOriginal(f,offset,mask,shiftedValue,isObject);
                    return;
                } else if (f.State == ObjState.Tainted &&
                           SwapObjectState(o,f.Clear(),f)) {
                    // -> The object was Tainted because of a concurrent
                    //    write, and we managed to pin it (because that's
                    //    our conservative way of handling writes that
                    //    happen at the same time as tainted writes).
                    
                    numTaintPins++;
                    NotifyPin(Magic.addressOf(o));
                    WriteWordOriginal(f,offset,mask,shiftedValue,isObject);
                    return;
                } else if (p==Phase.Prep &&
                           f.State==ObjState.Tagged &&
                           SwapObjectState(o,
                                           f.WithState(ObjState.Tainted),
                                           f)) {
                    // This means that we are (or were) in the Prep phase
                    // and tried to write into a Tagged object.  Since
                    // some threads may still be Idle, we cannot write by
                    // expanding the object - but at the same time we have
                    // to be aware of threads that may be in Copy, and so
                    // may be actively expanding objects.  The compromise is
                    // to taint the object.  This will prevent object
                    // expansion for the duration of the write.
                    WriteWordNoForward(o,offset,mask,shiftedValue,isObject);
                    
                    // The write has succeeded, so we attempt to untaint the
                    // object and make it tagged again.  Of course this
                    // will fail if a concurrent write had pinned the object.
                    SwapObjectState(o,f,f.WithState(ObjState.Tainted));
                    return;
                } else if (p==Phase.Copy &&
                           (f.State==ObjState.Tagged ||
                            f.State==ObjState.Expanded)) {
                    // Now we have the interesting case: we're in the Copy
                    // phase and we have an object that is either tagged
                    // for expansion or is already expanded.
                    
                    if (!ExpandIfNecessary(ref f,o)) {
                        continue;
                    }
                    
                    // Now we have a forwarding word that is
                    // guaranteed to have a reference to a wide
                    // object.  We know that the world is either in the
                    // Copy phase or in the Idle phase following the
                    // Copy phase.  At worst, the wide object is "defunct",
                    // meaning that all of the fields are in the InCopy
                    // state.  That's fine, since the wide object will
                    // have a reference to the to-space copy.
                    
                    WideObject wide=f.Wide;
                    WideWord ww=wide.words[ToIndex(offset)];
                    WordStatus stat=ww.status;
                    if (stat.InAction) {
                        wide.completeOneAction();
                    } else if (stat.State==WordState.InCopy) {
                        WriteWordNoForward(wide.copy,offset,mask,
                                           shiftedValue,isObject);
                        return;
                    } else if (stat.State==WordState.Original) {
                        if (fVerbose) {
                            VTable.DebugPrint("    ** copying field into wide object: from = ");
                            VTable.DebugPrint((ulong)Magic.addressOf(o));
                            VTable.DebugPrint(", wide = ");
                            VTable.DebugPrint((ulong)Magic.addressOf(wide));
                            VTable.DebugPrint(", offset = ");
                            VTable.DebugPrint((ulong)offset);
                            VTable.DebugPrint("\n");
                        }
                        UIntPtr oldVal=*(UIntPtr*)(Magic.addressOf(o)+offset);
                        if (isObject) {
                            TargetBarrierWithForward(oldVal);
                        }
                        if (wide.words[ToIndex(offset)]
                            .CAS(stat.WithState(WordState.InWide),
                                 (shiftedValue&mask)|(oldVal&~mask),
                                 stat,UIntPtr.Zero)) {
                            return;
                        }
                    } else /* stat.State==InWide */{
                        if (isObject) {
                            TargetBarrierWithForward(ww.payload);
                        }
                        if (wide.words[ToIndex(offset)]
                            .CAS(stat,(shiftedValue&mask)|(ww.payload&~mask),
                                 stat,ww.payload)) {
                            return;
                        }
                    }
                }
            }
        }
        
        static bool WeakCASWordNoForward(Object o,
                                         UIntPtr offset,
                                         UIntPtr mask,
                                         UIntPtr shiftedValue,
                                         UIntPtr shiftedComparand) {
            UIntPtr *ptr=(UIntPtr*)(Magic.addressOf(o)+offset);
            UIntPtr oldVal=*ptr;
            UIntPtr comparand = (oldVal&~mask)|(shiftedComparand&mask);
            return CAS(ptr,
                       (oldVal&~mask)|(shiftedValue&mask),
                       comparand)
                == comparand;
        }
        
        static bool WeakCASWordOriginal(ForwardingWord f,
                                        UIntPtr offset,
                                        UIntPtr mask,
                                        UIntPtr shiftedValue,
                                        UIntPtr shiftedComparand) {
            return WeakCASWordNoForward(f.Forward,offset,mask,
                                        shiftedValue,shiftedComparand);
        }
        
        [NoInline]
        [CalledRarely]
        protected override bool WeakCASWordSlow(Object o,
                                                UIntPtr offset,
                                                UIntPtr mask,
                                                UIntPtr shiftedValue,
                                                UIntPtr shiftedComparand,
                                                bool isObject) {
            // This is more-or-less modeled after WriteWordSlow, except
            // that it will fail spuriously.  Thus the large comment
            // blocks are removed.
            
            Phase p=phase;
            ForwardingWord f=GetForwardingWord(o);
            if (IgnoreOffset(offset)) {
                return WeakCASWordNoForward(o,offset,mask,
                                            shiftedValue,
                                            shiftedComparand);
            } else if (f.State==ObjState.SimpleOrForwarded ||
                       p==Phase.Idle) {
                return WeakCASWordOriginal(f,offset,mask,
                                           shiftedValue,
                                           shiftedComparand);
            } else if (f.State==ObjState.Tainted &&
                       SwapObjectState(o,f.Clear(),f)) {
                numTaintPins++;
                NotifyPin(Magic.addressOf(o));
                return WeakCASWordOriginal(f,offset,mask,
                                           shiftedValue,
                                           shiftedComparand);
            } else if (p==Phase.Prep &&
                       f.State==ObjState.Tagged &&
                       SwapObjectState(o,f.WithState(ObjState.Tainted),f)) {
                bool result=
                    WeakCASWordNoForward(o,offset,mask,
                                         shiftedValue,
                                         shiftedComparand);
                SwapObjectState(o,f,f.WithState(ObjState.Tainted));
                return result;
            } else if (p==Phase.Copy &&
                       (f.State==ObjState.Tagged ||
                        f.State==ObjState.Expanded)) {
                // Now we have the interesting case: we're in the Copy
                // phase and we have an object that is either tagged
                // for expansion or is already expanded.
                
                if (!ExpandIfNecessary(ref f,o)) {
                    return false;
                }
                    
                WideObject wide=f.Wide;
                WideWord ww=wide.words[ToIndex(offset)];
                WordStatus stat=ww.status;
                if (stat.InAction) {
                    wide.completeOneAction();
                } else if (stat.State==WordState.InCopy) {
                    return WeakCASWordNoForward(wide.copy,offset,mask,
                                                shiftedValue,
                                                shiftedComparand);
                } else if (stat.State==WordState.Original) {
                    UIntPtr oldVal=*(UIntPtr*)(Magic.addressOf(o)+offset);
                    if ((oldVal&mask)!=(shiftedComparand&mask)) {
                        return false;
                    }
                    return wide.words[ToIndex(offset)]
                        .CAS(stat.WithState(WordState.InWide),
                             (oldVal&~mask)|(shiftedValue&mask),
                             stat,UIntPtr.Zero);
                } else /* stat.State == InWide */ {
                    return wide.words[ToIndex(offset)]
                        .CAS(stat,(ww.payload&~mask)|(shiftedValue&mask),
                             stat,(ww.payload&~mask)|(shiftedComparand&mask));
                }
            }
            return false;
        }
        
        static bool WeakCASArbitraryNoForward(Object o,
                                              UIntPtr offset,
                                              UIntPtr size,
                                              ulong value,
                                              ulong comparand) {
            UIntPtr ptr=Magic.addressOf(o)+offset;
            if (size==4) {
                return CAS((int*)ptr,(int)value,(int)comparand)
                    == (int)comparand;
            } else if (size==8) {
                return CAS((long*)ptr,(long)value,(long)comparand)
                    == (long)comparand;
            } else {
                VTable.NotReached();
                return false;
            }
        }
        
        static bool WeakCASArbitraryOriginal(ForwardingWord f,
                                             UIntPtr offset,
                                             UIntPtr size,
                                             ulong value,
                                             ulong comparand) {
            return WeakCASArbitraryNoForward(f.Forward,offset,size,
                                             value,comparand);
        }
        
        [NoInline]
        [CalledRarely]
        protected override bool WeakCASArbitrarySlow(Object o,
                                                     UIntPtr offset,
                                                     UIntPtr size,
                                                     ulong value,
                                                     ulong comparand) {
            Phase p=phase;
            ulong pv=CurThreadPhaseVersion;
            ForwardingWord f=GetForwardingWord(o);
            if (f.State==ObjState.SimpleOrForwarded ||
                p==Phase.Idle) {
                return WeakCASArbitraryOriginal(f,offset,size,
                                                value,
                                                comparand);
            } else if (f.State==ObjState.Tainted &&
                       SwapObjectState(o,f.Clear(),f)) {
                numTaintPins++;
                NotifyPin(Magic.addressOf(o));
                return WeakCASArbitraryOriginal(f,offset,size,
                                                value,
                                                comparand);
            } else if (p==Phase.Prep &&
                       f.State==ObjState.Tagged &&
                       SwapObjectState(o,f.WithState(ObjState.Tainted),f)) {
                bool result=
                    WeakCASArbitraryNoForward(o,offset,size,
                                              value,
                                              comparand);
                SwapObjectState(o,f,f.WithState(ObjState.Tainted));
                return result;
            } else if (p==Phase.Copy &&
                       (f.State==ObjState.Tagged ||
                        f.State==ObjState.Expanded)) {
                if (!ExpandIfNecessary(ref f,o)) {
                    return false;
                }
                
                WideObject wide=f.Wide;
                
                UIntPtr maxLowOff=(UIntPtr)sizeof(UIntPtr);
                UIntPtr lowMask=maxLowOff-1;
                UIntPtr lowOff=offset&lowMask;
                UIntPtr baseOff=offset&~lowMask;
                UIntPtr tailOff=(offset+size+lowMask)&~lowMask;
                
                // check what the deal is with field states.
                // if all fields are copied, then we just do
                // a CAS directly on the to-space copy.  if
                // none of the fields are copied then we do
                // an action-CAS.  else we completeOneAction()
                // and fail.
                bool foundNotCopied=false;
                bool foundCopied=false;
                for (UIntPtr i=baseOff;i<tailOff;++i) {
                    WordState s=wide.words[ToIndex(i)].status.State;
                    if (s!=WordState.InCopy) {
                        foundNotCopied=true;
                    }
                    if (s==WordState.InCopy) {
                        foundCopied=true;
                    }
                }
                
                if (foundNotCopied && foundCopied) {
                    wide.completeOneAction();
                    return false;
                } else if (!foundNotCopied) {
                    // they're all copied - do direct CAS on the
                    // to-space copy
                    return WeakCASArbitraryNoForward(wide.copy,
                                                     offset,
                                                     size,
                                                     value,
                                                     comparand);
                } else /* !foundCopied */ {
                    // none of them are copied - do an action-CAS

                    // DANGER! this is a safepoint!
                    Action a=new Action((uint)(tailOff-baseOff));
                    
                    // check if the world has changed
                    if (CurThreadPhaseVersion != pv) {
                        return false;
                    }

                    for (UIntPtr i=baseOff;i<tailOff;++i) {
                        WideWord ww=wide.words[ToIndex(i)];
                        
                        if (ww.status.State==WordState.InCopy ||
                            ww.status.InAction) {
                            // no good - give up and try again, but
                            // try to completeOneAction for good
                            // measure.
                            wide.completeOneAction();
                            return false;
                        }
                        
                        UIntPtr oldVal;
                        
                        if (ww.status.State == WordState.Original) {
                            oldVal = *(UIntPtr*)(Magic.addressOf(o) + i);
                        } else {
                            oldVal = ww.payload;
                        }
                        
                        // offsetIntoField tells us the position of
                        // i in the field we're CASing.  this may be
                        // negative
                        int begin=(int)(i-offset);
                        int end=(int)(i+(UIntPtr)sizeof(UIntPtr)-offset);
                        
                        UIntPtr curValueWord=UIntPtr.Zero;
                        UIntPtr curComparandWord=UIntPtr.Zero;
                        UIntPtr curWordMask=UIntPtr.Zero;
                        
                        // what follows is pure genius
                        byte *valuePtr=
                            (byte*)Magic.toPointer(ref value);
                        byte *comparandPtr=
                            (byte*)Magic.toPointer(ref comparand);
                        if (instance.BigEndian) {
                            valuePtr+=(UIntPtr)8-size;
                            comparandPtr+=(UIntPtr)8-size;
                        }
                        valuePtr+=begin;
                        comparandPtr+=begin;
                        byte *curValueWordPtr=
                            (byte*)Magic.toPointer(ref curValueWord);
                        byte *curComparandWordPtr=
                            (byte*)Magic.toPointer(ref curComparandWord);
                        byte *curWordMaskPtr=
                            (byte*)Magic.toPointer(ref curWordMask);
                        // this loop is not very quick, but then again,
                        // it doesn't have to be at this point.
                        for (int j=begin;j<end;++j) {
                            if (j>=0 && j<(int)size) {
                                *curValueWordPtr=*valuePtr;
                                *curComparandWordPtr=*comparandPtr;
                                *curWordMaskPtr=255;
                            }
                            valuePtr++;
                            comparandPtr++;
                            curValueWordPtr++;
                            curComparandWordPtr++;
                            curWordMaskPtr++;
                        }
                        
                        a.words[(int)((i-baseOff)/(uint)sizeof(UIntPtr))]
                            =new WordAction(ToIndex(i),
                                            ww.status.WithState(WordState.InWide),
                                            (curValueWord&curWordMask)
                                            |(oldVal&~curWordMask),
                                            ww.status,
                                            (curComparandWord&curWordMask)
                                            |(oldVal&~curWordMask));
                    }
                    
                    // really work hard to try to install this action -
                    // it took enough effort to build that giving up
                    // would be silly.
                    while (CAS(ref wide.action,a,null) != null) {
                        wide.completeOneAction();
                    }
                    
                    // this either completes our action or some action
                    // that follows it.
                    wide.completeOneAction();
                    
                    // our action must be complete here.  if it isn't then
                    // it's a bug and we should abort.
                    if (a.Res==ActionResult.None) {
                        VTable.NotReached();
                    }
                    
                    return a.Res==ActionResult.Success;
                } /* !foundCopied */
            } /* p==Copy &&
                 (f.state==Tagged ||
                  f.state==Expanded) */

            return false;
        }
        
        internal static WideObject wideHead;
        
        internal override bool AnyTaggedForCopying {
            get {
                return wideHead!=null;
            }
        }
        
        internal override bool TagObjectForCopy(Object from,
                                                Object to,
                                                out UIntPtr spaceOverhead)
        {
            WideObject wide=
                new WideObject(wideHead,
                               from,
                               to);
            spaceOverhead=wide.spaceOverhead;
            if (fVerbose) {
                VTable.DebugPrint("   $$ tagging object ");
                VTable.DebugPrint((ulong)Magic.addressOf(from));
                VTable.DebugPrint(", wide = ");
                VTable.DebugPrint((ulong)Magic.addressOf(wide));
                VTable.DebugPrint(", copy = ");
                VTable.DebugPrint((ulong)Magic.addressOf(to));
                VTable.DebugPrint("\n");
            }
            if (SwapObjectState(from,
                                new ForwardingWord(from,
                                                   ObjState.Tagged,
                                                   wide),
                                new ForwardingWord(from,
                                                   UIntPtr.Zero))) {
                wideHead=wide;
                return true;
            } else {
                if (fDebug) {
                    VTable.DebugPrint("   did not tag object because the CAS on the forwarding word failed\n");
                }
                return false;
            }
        }

        internal override bool NeedsPrepPhase {
            get {
                return true;
            }
        }
        
        [NoBarriers]
        internal override ulong Copy()
        {
            if (fDebug) {
                VTable.DebugPrint("     --> CoCo in Copy\n");
            }

            ulong numAttempted=0, numCopied=0, numActionCopied=0;
            WideObject wideHead=ExpandingCoCoBarrier.wideHead;
            ExpandingCoCoBarrier.wideHead=null;
            for (WideObject wide=wideHead;
                 wide!=null;
                 wide=wide.next) {

                numAttempted++;

                Object from=wide.from;

                if (fGorierCopy && from==interlock) {
                    VTable.DebugPrint("     AWESOME: attempting to move interlock from ");
                    VTable.DebugPrint((ulong)Magic.addressOf(interlock));
                    VTable.DebugPrint(" to ");
                    VTable.DebugPrint((ulong)Magic.addressOf(wide.copy));
                    VTable.DebugPrint("\n");
                }
                
                if (fGorierCopy) {
                    VTable.DebugPrint("      ---> operating on ");
                    VTable.DebugPrint((ulong)Magic.addressOf(wide));
                    VTable.DebugPrint(" (from = ");
                    VTable.DebugPrint((ulong)Magic.addressOf(wide.from));
                    VTable.DebugPrint(", copy = ");
                    VTable.DebugPrint((ulong)Magic.addressOf(wide.copy));
                    VTable.DebugPrint(")\n");
                }

                ForwardingWord f;
                for (long cnt=0;;cnt++) {
                    f=GetForwardingWord(from);
                    if (cnt>10 && fDebug) {
                        VTable.DebugPrint("     for ");
                        VTable.DebugPrint((ulong)Magic.addressOf(from));
                        VTable.DebugPrint(", forwarding word = ");
                        VTable.DebugPrint((ulong)f.Bits);
                        VTable.DebugPrint("\n");
                    }
                    if (f.State==ObjState.Tainted ||
                        (f.State==ObjState.Tagged &&
                         ShouldPin(Magic.addressOf(from)))) {
                        numTaintPins++;
                        NotifyPin(Magic.addressOf(from));
                        SwapObjectState(from,f.Clear(),f);
                    } else if (f.State==ObjState.SimpleOrForwarded ||
                               f.State==ObjState.Expanded) {
                        break;
                    } else if (f.State==ObjState.Tagged) {
                        SwapObjectState(from,f.WithState(ObjState.Expanded),f);
                    }
                }
                if (f.State!=ObjState.Expanded) {
                    continue;
                }
                
                if (fGorierCopy && from==interlock) {
                    VTable.DebugPrint("     AWESOME: moving interlock from ");
                    VTable.DebugPrint((ulong)Magic.addressOf(interlock));
                    VTable.DebugPrint(" to ");
                    VTable.DebugPrint((ulong)Magic.addressOf(wide.copy));
                    VTable.DebugPrint("\n");
                }
                
                if (fVerboseCopy) {
                    VTable.DebugPrint("           - actually copying ");
                    VTable.DebugPrint((ulong)Magic.addressOf(wide));
                    VTable.DebugPrint(" (from = ");
                    VTable.DebugPrint((ulong)Magic.addressOf(wide.from));
                    VTable.DebugPrint(", copy = ");
                    VTable.DebugPrint((ulong)Magic.addressOf(wide.copy));
                    VTable.DebugPrint(")\n");
                }

                // copy fields into wide object
                for (int i=0;i<wide.words.Length;++i) {
                    UIntPtr offset=ToOffset(i);
                    if (IgnoreOffset(offset)) {
                        continue;
                    }
                    for (;;) {
                        UIntPtr val=*(UIntPtr*)
                            (Magic.addressOf(from) + offset);
                                
                        WordStatus oldStatus=wide.words[i].status;
                        if (oldStatus.InAction) {
                            wide.completeOneAction();
                        } else if (oldStatus.State
                                   !=WordState.Original) {
                            break;
                        } else if (wide.words[i]
                                   .CAS(oldStatus.WithState(WordState.InWide),
                                        val,
                                        oldStatus,
                                        UIntPtr.Zero)) {
                            break;
                        }
                    }
                }

                bool didActionCopy=false;
                        
                // copy fields from wide object into to-space
                // object
                if (fGorierCopy) {
                    VTable.DebugPrint("                 - copying:");
                }
                for (int i=0;i<wide.words.Length;i++) {
                    UIntPtr offset=ToOffset(i);
                    if (IgnoreOffset(offset)) {
                        // ignore
                    } else if (// check that we're not in the header.  the
                               // header is not necessarily double-word aligned, and
                               // we ASSUME that it contains no double-words, so
                               // we should not be doing double-word copies there.
                               // Note that we use sign comparison because we want the
                               // offsets into the pre header to appear negative.
                               ((IntPtr)offset)>=(IntPtr)PostHeader.Size &&
                               
                               // there have to be two or more words left for us to
                               // do a double-word copy.
                               i+1<wide.words.Length &&
                               
                               // check that the alignment of the object is at least
                               // double word.  otherwise we know that there are no
                               // double words and so a double-word copy is not
                               // needed.
                               from.vtable.baseAlignment>=UIntPtr.Size*2) {

                        if (fGorierCopy) {
                            VTable.DebugPrint("\n*** using action-copy ***\n");
                        }
                        didActionCopy=true;

                        // double-word copying needed
                        UIntPtr *trg=(UIntPtr*)
                            (Magic.addressOf(wide.copy) + offset);
                        for (;;) {
                            WordStatus s1 = wide.words[i+0].status;
                            UIntPtr p1    = wide.words[i+0].payload;

                            WordStatus s2 = wide.words[i+1].status;
                            UIntPtr p2    = wide.words[i+1].payload;

                            if (s1.InAction || s2.InAction) {
                                wide.completeOneAction();
                                continue;
                            }
                            
                            trg[0] = p1;
                            trg[1] = p2;
                            
                            Action a = new Action(2);

                            a.words[0].index            = i+0;
                            a.words[0].statusValue      = s1.WithState(WordState.InCopy);
                            a.words[0].payloadValue     = p1;
                            a.words[0].statusComparand  = s1;
                            a.words[0].payloadComparand = p1;

                            a.words[1].index            = i+1;
                            a.words[1].statusValue      = s2.WithState(WordState.InCopy);
                            a.words[1].payloadValue     = p2;
                            a.words[1].statusComparand  = s2;
                            a.words[1].payloadComparand = p2;
                            
                            while (CAS(ref wide.action,a,null) != null) {
                                wide.completeOneAction();
                            }
                            
                            wide.completeOneAction();
                            
                            if (a.Res == ActionResult.None) {
                                VTable.NotReached();
                            }
                            
                            if (a.Res == ActionResult.Success) {
                                break;
                            }
                        }
                        
                        i++;
                    } else {
                        // only need single-word copying
                        UIntPtr *trg=(UIntPtr*)
                            (Magic.addressOf(wide.copy) + offset);
                        for (;;) {
                            WideWord ww=wide.words[i];
                            if (ww.status.InAction) {
                                // this is highly unlikely
                                wide.completeOneAction();
                                continue;
                            }
                            *trg=ww.payload;
                            if (wide.words[i]
                                .CAS(ww.status.WithState(WordState.InCopy),
                                     ww.payload,
                                     ww.status,
                                     ww.payload)) {
                                if (fGorierCopy) {
                                    VTable.DebugPrint(" [");
                                    VTable.DebugPrint((ulong)offset);
                                    VTable.DebugPrint(", ");
                                    VTable.DebugPrint((ulong)ww.payload);
                                    VTable.DebugPrint("]");
                                }
                                break;
                            }
                        }
                    }
                }
                
                if (fGorierCopy) {
                    VTable.DebugPrint("\n");
                }
                
                if (didActionCopy) {
                    numActionCopied++;
                }
                
                // finish up for this object
                ForwardingWord newf=
                    f.WithState(ObjState.SimpleOrForwarded)
                     .WithForward(wide.copy);
                
                bool res = SwapObjectState(from,newf,f);
                if (fGorierCopy) {
                    VTable.DebugPrint("          --> res = ");
                    VTable.DebugPrint(res);
                    VTable.DebugPrint("\n");
                }
                VTable.Assert(res, "object transitioned out of expanded without our approval");
                
                numCopied++;
                
                if (fDebug && (numAttempted%10000)==0) {
                    VTable.DebugPrint("      ---> copied ");
                    VTable.DebugPrint(numCopied);
                    VTable.DebugPrint(" / ");
                    VTable.DebugPrint(numAttempted);
                    VTable.DebugPrint("\n");
                }
            }
            if (fDebug) {
                VTable.DebugPrint("     --> copied ");
                VTable.DebugPrint(numCopied);
                VTable.DebugPrint(" / ");
                VTable.DebugPrint(numAttempted);
                VTable.DebugPrint("; ");
                VTable.DebugPrint(numActionCopied);
                VTable.DebugPrint(" action-copied\n");
            }
            
            return numCopied;
        }
    }
}

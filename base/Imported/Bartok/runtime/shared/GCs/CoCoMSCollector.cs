/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace System.GCs {

    using Microsoft.Bartok.Runtime;
    using System.Runtime.CompilerServices;
    using System.Threading;

#if SINGULARITY
    using Microsoft.Singularity;
#if SINGULARITY_PROCESS
    using Microsoft.Singularity.V1.Services; // Used for timing, only
#elif SINGULARITY_KERNEL
    using Microsoft.Singularity.Scheduling;
    using Microsoft.Singularity.X86;
#endif
#endif
    
    using Microsoft.Win32;

    [NoCCtor]
    [RequiredByBartok]
    internal class CoCoMSCollector: ConcurrentMSCollector
    {
        internal static new CoCoMSCollector instance;
        
        internal static Thread cocoThread;
        
        internal static bool didStartTrace;
        internal static bool didEndTrace;
        internal static bool wantCoCo;
        internal static bool doingCoCo;
        internal static int markingForCoCo; // actually a boolean
        internal static bool inFixUp;
        internal static bool die;
        internal static ulong numCopied;
        internal static int delayCnt;
        internal static Object interlock;
        
        internal static int pinTime;
        internal static int prepTime;
        internal static int copyTime;
        internal static int forwardTime;
        
        internal static int timingBefore;
        internal static int timingAfterPin;
        internal static int timingAfterPrep;
        internal static int timingAfterCopy;
        internal static int timingAfter;
        
        internal static UIntPtr maxSpaceOverhead;
        
        internal static int sizeFracLim;
        internal static int sizeLim;
        internal static int pageFragThres;
        internal static int pinPenalty;
        internal static int cocoDelay;
        
        internal static UIntPtr lastSmallPagesRecycle;
        
        internal static NonNullReferenceVisitor normalStackMarker;
        internal static NonNullReferenceVisitor nopStackMarker;
        internal static NonNullReferenceVisitor pinStackMarker;
        
        [NoBarriers]
        [PreInitRefCounts]
        public static new void Initialize()
        {
            ConcurrentMSCollector.InitializeAllButVisitors();
            // instance = new CoCoMSCollector();
            ConcurrentMSCollector.instance
                = CoCoMSCollector.instance
                = (CoCoMSCollector)
                BootstrapMemory.Allocate(typeof(CoCoMSCollector));
            ConcurrentMSCollector.markReferenceVisitor =
                (MarkReferenceVisitor)
                BootstrapMemory.Allocate(typeof(MarkAndForwardReferenceVisitor));
            CoCoMSCollector.normalStackMarker =
                (NonNullReferenceVisitor)
                BootstrapMemory.Allocate(typeof(StackForwardReferenceVisitor));
            CoCoMSCollector.pinStackMarker =
                (NonNullReferenceVisitor)
                BootstrapMemory.Allocate(typeof(StackMarkPinnedReferenceVisitor));
            CoCoMSCollector.nopStackMarker =
                (NonNullReferenceVisitor)
                BootstrapMemory.Allocate(typeof(StackNopReferenceVisitor));
            ConcurrentMSCollector.stackMarkReferenceVisitor =
                CoCoMSCollector.normalStackMarker;
            ConcurrentMSCollector.stackMarkPinnedReferenceVisitor =
                CoCoMSCollector.normalStackMarker;
            ConcurrentMSCollector.updateReferenceVisitor =
                (UpdateReferenceVisitor)
                BootstrapMemory.Allocate(typeof(UpdateAndForwardReferenceVisitor));
            ConcurrentMSCollector.partialFreePageVisitor =
                (SegregatedFreeList.PartialFreePageVisitor)
                BootstrapMemory.Allocate(typeof(TaggingPartialFreePageVisitor));
            // sweepVisitor = new SweepVisitor();
            sweepVisitor = (SweepVisitor)
                BootstrapMemory.Allocate(typeof(SweepVisitor));
        }

        internal static int EnvInt(int defVal,
                                   string name)
        {
            string str=Environment.GetEnvironmentVariable(name);
            if (str==null) {
                return defVal;
            } else {
                return Int32.Parse(str);
            }
        }
        
        internal override void EnableHeap()
        {
            interlock=new Object();
            MultiUseWord.GetMonitor(interlock);
            CoCoBarrier.InitLate();
            
            // REVIEW: add some bartok args instead
            
            sizeFracLim   = EnvInt( 10 , "COCO_SIZE_FRAC_LIM"   );
            sizeLim       = EnvInt( -1 , "COCO_SIZE_LIM"        );
            pageFragThres = EnvInt(  2 , "COCO_PAGE_FRAG_THRES" );
            pinPenalty    = EnvInt( 10 , "COCO_PIN_PENALTY"     );
            cocoDelay     = EnvInt(  8 , "COCO_COPY_DELAY"      );
            
            if (EnvInt(0,"COCO_FORCE_SLOW")!=0) {
                CoCoBarrier.ForceSlow();
            }
            if (EnvInt(0,"COCO_FORCE_NOT_IDLE")!=0) {
                CoCoBarrier.ForceNotIdle();
            }
            if (EnvInt(0,"COCO_FORCE_FORWARDING")!=0) {
                CoCoBarrier.ForceForwarding();
            }
            if (EnvInt(0,"COCO_FORCE_PINNING")!=0) {
                CoCoBarrier.ForcePinning();
            }
            
            base.EnableHeap();
            cocoThread=new Thread(new ThreadStart(CoCoLoop));
            cocoThread.Start();
        }
        
        internal override void Shutdown()
        {
            base.Shutdown();
            lock (interlock) {
                die = true;
                Monitor.PulseAll(interlock);
            }
            cocoThread.Join();
            if (VTable.enableFinalGCTiming) {
                VTable.DebugPrint("CoCo completed ");
                VTable.DebugPrint(cycles);
                VTable.DebugPrint(" cycles, started ");
                VTable.DebugPrint(cyclesStarted);
                VTable.DebugPrint(" cycles, and copied ");
                VTable.DebugPrint(numCopied);
                VTable.DebugPrint(" objects.\n");
                VTable.DebugPrint("CoCo took ");
                VTable.DebugPrint((ulong)pinTime);
                VTable.DebugPrint("+");
                VTable.DebugPrint((ulong)prepTime);
                VTable.DebugPrint("+");
                VTable.DebugPrint((ulong)copyTime);
                VTable.DebugPrint("+");
                VTable.DebugPrint((ulong)forwardTime);
                VTable.DebugPrint("=");
                VTable.DebugPrint((ulong)(pinTime+prepTime+copyTime+forwardTime));
                VTable.DebugPrint(" ms.\n");
                VTable.DebugPrint("max space overhead = ");
                VTable.DebugPrint((ulong)maxSpaceOverhead);
                VTable.DebugPrint("\n");
                CoCoBarrier.PrintStats();
            }
        }
        
        internal override void ThreadStartNotification(int currentThreadIndex)
        {
            base.ThreadStartNotification(currentThreadIndex);
            CoCoBarrier.ThreadStart(Thread.threadTable[currentThreadIndex]);
        }
        
        internal override UIntPtr AllocateObjectMemorySlow(UIntPtr numBytes,
                                                           uint alignment,
                                                           Thread currentThread)
        {
            CoCoBarrier.ClientHandshake();
            return base.AllocateObjectMemorySlow(numBytes,
                                                 alignment,
                                                 currentThread);
        }
        
        internal static void InterlockWithCopier(ref bool condition)
        {
            lock (interlock) {
                if (fVerbose) {
                    VTable.DebugPrint("      ~~ acquired lock, setting condition\n");
                }
                condition = true;
                if (fVerbose) {
                    VTable.DebugPrint("      ~~ pulsing = ");
                    VTable.DebugPrint((ulong)Magic.addressOf(interlock));
                    VTable.DebugPrint("\n");
                }
                Monitor.PulseAll(interlock);
                if (fVerbose) {
                    VTable.DebugPrint("      ~~ waiting\n");
                }
                while (condition) {
                    Monitor.Wait(interlock);
                }
            }
        }
        
        internal override void PreTraceHook()
        {
            if (fVerbose) {
                VTable.DebugPrint("  ~~~~~ PreTraceHook ~ waiting\n");
            }
            InterlockWithCopier(ref didStartTrace);
            if (fVerbose) {
                VTable.DebugPrint("  ~~~~~ PreTraceHook ~ awoken\n");
            }
        }
        
        internal override void PostRootScanHook()
        {
            if (inFixUp) {
                timingAfterCopy = Environment.TickCount;
                CoCoBarrier.ChangePhase(CoCoBarrier.Phase.Idle,true,true);
            }
        }
        
        internal override void PostTraceHook()
        {
            if (fVerbose) {
                VTable.DebugPrint("  ~~~~~ PostTraceHook ~ waiting\n");
            }
            InterlockWithCopier(ref didEndTrace);
            if (fVerbose) {
                VTable.DebugPrint("  ~~~~~ PostTraceHook ~ awoken\n");
            }
        }
        
        internal override void PostReclamationHook()
        {
        }

        internal override void PreSweepHook()
        {
            CoCoBarrier.ExchangeReadyForCoCo(false);
        }
        
        internal override void PostSweepHook()
        {
            CoCoBarrier.ExchangeReadyForCoCo(true);
        }
        
        internal static void CoCoLoop()
        {
            if (fDebug) {
                VTable.DebugPrint("coco thread = ");
                VTable.DebugPrint((ulong)Win32Native.GetCurrentThreadId());
                VTable.DebugPrint("\n");
                VTable.DebugPrint("CoCo at ");
                VTable.DebugPrint((ulong)Magic.addressOf(Thread.CurrentThread));
                VTable.DebugPrint("\n");
            }
            for (;;) {
                lock (interlock) {
                    doingCoCo=false;
                    for (;;) {
                        if (die) {
                            return;
                        } else if (didStartTrace) {
                            didStartTrace=false;
                            Monitor.PulseAll(interlock);
                        } else if (didEndTrace) {
                            didEndTrace=false;
                            Monitor.PulseAll(interlock);
                            if (wantCoCo) {
                                break;
                            }
                        }
                        Monitor.Wait(interlock);
                    }
                    wantCoCo=false;
                }
                
                // now further tracing is BLOCKED
                
                cyclesStarted++;
                timingBefore = Environment.TickCount;
                
                if (fDebug) {
                    VTable.DebugPrint("+++++ Start Concurrent Copying\n");
                }
                
                CoCoBarrier.EnablePinning();
                doingCoCo=true;
                ConcurrentMSCollector.stackMarkReferenceVisitor =
                    CoCoMSCollector.nopStackMarker;
                ConcurrentMSCollector.stackMarkPinnedReferenceVisitor =
                    CoCoMSCollector.pinStackMarker;
                // Perform a scan of all call stacks, including the call
                // stack of the CoCo thread.
                ConcurrentMSCollector.TrivialHandshake = false;
                ConcurrentMSCollector.IncludeMUWInHandshake = false;
                ConcurrentMSCollector.CollectorHandshake(cocoThread);
                // In order to scan the call stack of the current thread,
                // we need a TransitionRecord for the thread.  At this
                // point we don't have one, so we have to go through
                // CollectBodyTransition to get one.
                Transitions.MakeGCRequest(cocoThread.threadIndex);
                GC.InvokeCollection(cocoThread);
                ConcurrentMSCollector.TrivialHandshake = true;
                ConcurrentMSCollector.IncludeMUWInHandshake = true;
                ConcurrentMSCollector.stackMarkReferenceVisitor =
                    CoCoMSCollector.normalStackMarker;
                ConcurrentMSCollector.stackMarkPinnedReferenceVisitor =
                    CoCoMSCollector.normalStackMarker;
                
                timingAfterPin = Environment.TickCount;
                
                if (fDebug) {
                    VTable.DebugPrint("+++++ Copying\n");
                }
                
                if (CoCoBarrier.instance.NeedsPrepPhase) {
                    CoCoBarrier.ChangePhase(CoCoBarrier.Phase.Prep,false,true);
                }
                
                timingAfterPrep = Environment.TickCount;
                
                CoCoBarrier.ChangePhase(CoCoBarrier.Phase.Copy,true,true);
            
                numCopied+=CoCoBarrier.instance.Copy();

                CoCoBarrier.ChangePhase(CoCoBarrier.Phase.Fixup,true,true);

                AddCollectionRequest();

                // wait for a complete collector cycle.  This is for fixup.
                if (fDebug) {
                    VTable.DebugPrint("+++++ Fixup: Waiting to start tracing\n");
                }
                lock (interlock) {
                    while (!didStartTrace && !die) {
                        Monitor.Wait(interlock);
                    }
                    if (die) {
                        return;
                    }
                    didStartTrace=false;
                    inFixUp=true;
                    Monitor.PulseAll(interlock);
                }

                if (fDebug) {
                    VTable.DebugPrint("+++++ Fixup: Waiting to end tracing\n");
                }
                lock (interlock) {
                    while (!didEndTrace && !die) {
                        Monitor.Wait(interlock);
                    }
                    if (die) {
                        return;
                    }
                    didEndTrace=false;
                    doingCoCo=false;
                    inFixUp=false;
                    Monitor.PulseAll(interlock);
                }
                
                timingAfter = Environment.TickCount;

                CoCoBarrier.ChangePhase(CoCoBarrier.Phase.Idle,false,false);
                
                if (fDebug) {
                    VTable.DebugPrint("+++++ Finish Concurrent Copying\n");
                }
                
                pinTime+=(timingAfterPin-timingBefore);
                prepTime+=(timingAfterPrep-timingAfterPin);
                copyTime+=(timingAfterCopy-timingAfterPrep);
                forwardTime+=(timingAfter-timingAfterCopy);
                
                cycles++;
            }
        }

        internal class MarkAndForwardReferenceVisitor : MarkReferenceVisitor
        {
            [NoBarriers]
            ulong cnt;
            [NoBarriers]
            bool amMarkingForCoCo;
            [NoBarriers]
            UIntPtr spaceOverhead;
            
            internal override void Init()
            {
                base.Init();
                cnt=0;
                amMarkingForCoCo=(markingForCoCo!=0);
                spaceOverhead=UIntPtr.Zero;
                if (fDebug && amMarkingForCoCo) {
                    VTable.DebugPrint("+++++ Marking For CoCo\n");
                }
            }

            internal override void Cleanup()
            {
                base.Cleanup();
                if (spaceOverhead>maxSpaceOverhead) {
                    maxSpaceOverhead=spaceOverhead;
                }
                if (amMarkingForCoCo) {
                    markingForCoCo=0;
#if !ARM && !ISA_ARM
                    // HACK: MemoryBarrier is unimplemented in ARM 
                    // and causes compile-time failures when building
                    // mscorlib in sepcomp mode. This change will break
                    // CoCo if built with ARM.
                    Thread.MemoryBarrier();
#endif
                }
                if (fDebug) {
                    VTable.DebugPrint("    $$$ tagged ");
                    VTable.DebugPrint(cnt);
                    VTable.DebugPrint(" objects\n");
                }
            }
            
            [NoInline]
            internal unsafe void ForwardAndVisit(UIntPtr *loc)
            {
                UIntPtr addr=*loc;
                if (addr==UIntPtr.Zero) {
                    return;
                }
                UIntPtr forward=
                    CoCoBarrier.instance.ToSpaceImplNonNull(Magic.fromAddress(addr));
                if (forward != addr) {
                    CoCoBarrier.CAS(loc,forward,addr);
                    // if this CAS fails it means that someone stored
                    // a different pointer into the field, but in that
                    // case the pointer stored would have already been
                    // forwarded thanks to the CoCo write barrier.
                }
                VisitValueNonNull(forward);
            }

            [Inline]
            protected override unsafe
            void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
            {
                this.Visit(location);
            }

            /// <summary>
            /// Visit an object reference.
            /// </summary>
            [Inline]
            internal unsafe override void Visit(UIntPtr *loc)
            {
                if (CoCoBarrier.forwarding) {
                    ForwardAndVisit(loc);
                } else {
                    VisitValueMaybeNull(*loc);
                }
            }
            
            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            [Inline]
            internal override UIntPtr VisitReferenceFields(Object obj)
            {
                return this.VisitReferenceFields(Magic.addressOf(obj),
                                                 obj.vtable);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            [Inline]
            internal override
            UIntPtr VisitReferenceFields(UIntPtr objectBase, VTable vtable)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, objectBase);
                return VisitReferenceFieldsTemplate(ref objDesc);
            }

            [NoInline]
            //[NoBarriers]
            void ProcessObjectsSlow(ref ThreadHeaderQueue.LocalList workList)
            {
                while (!ConcurrentMSCollector.killCollectorThreads
                       && !workList.IsEmpty()) {
                    // Pop the next value
                    Object obj = workList.Pop(markedColor);
                    if (fVerbose) {
                        VTable.DebugPrint("cms popped: ");
                        VTable.DebugPrint((ulong)Magic.addressOf(obj));
                        VTable.DebugPrint("\n");
                    }
                    // let CoCo do some stuff
                    ScanHook(obj);
                    // Visit Fields
                    this.VisitReferenceFields(obj);
                }
            }

            //[NoBarriers]
            internal override
            void ProcessMyGrayObjects(ref ThreadHeaderQueue.LocalList workList)
            {
                if (amMarkingForCoCo) {
                    ProcessObjectsSlow(ref workList);
                } else {
                    // hand-inlined from ConcurrentMSCollector.  needed
                    // to ensure that the VisitReferenceFields call gets
                    // inlined.
                    while (!ConcurrentMSCollector.killCollectorThreads
                           && !workList.IsEmpty()) {
                        // Pop the next value
                        Object obj = workList.Pop(markedColor);
                        if (CoCoBarrier.fVerifyToSpaceMark &&
                            !CoCoBarrier.instance.IsInToSpace(Magic.addressOf(obj))) {
                            VTable.DebugBreak();
                        }
                        // Visit Fields
                        this.VisitReferenceFields(obj);
                    }
                }
            }
            
            internal unsafe void ScanHook(Object obj)
            {
                UIntPtr page=PageTable.Page(Magic.addressOf(obj));
                if (PageTable.Type(page)!=SegregatedFreeList.SMALL_OBJ_PAGE) {
                    //VTable.DebugPrint("   not tagging because this isn't a small object page");
                    return;
                }
                SegregatedFreeList.PageHeader *ph=
                    (SegregatedFreeList.PageHeader*)PageTable.PageAddr(page);
                if (!new CoCoPageUserValue(ph->userValue).Marked) {
                    //VTable.DebugPrint("   not tagging because the page isn't marked\n");
                    return;
                }
                if (obj is EMU ||
                    obj is Monitor ||
                    obj is Thread ||
                    obj is ThreadHeaderQueue) {
                    CoCoBarrier.NotifyPin(Magic.addressOf(obj));
                    if (fVerbose) {
                        VTable.DebugPrint("      $$ not tagging object because it's a monitor or EMU\n");
                    }
                    return;
                }
                if (doingCoCo) {
                    //VTable.DebugPrint("   not tagging object because doingCoCo\n");
                    return;
                }
                if (!CoCoBarrier.instance.ObjectIsNotCopied(obj)) {
                    if (fVerbose) {
                        VTable.DebugPrint("   not tagging object because object is already in the process of being copied.\n");
                    }
                    return;
                }
                
                if (fVerbose && obj.GetType() != typeof(Object)) {
                    VTable.DebugPrint("    $$ tagging a non-System.Object; type is ");
                    VTable.DebugPrint(obj.GetType().Name);
                    VTable.DebugPrint("\n");
                }
                
                // REVIEW: I wish that there was an easier way of
                // doing this.
                Object copy;
                if (obj is Array) {
                    Array a=(Array)obj;
                    if (a.IsVector) {
                        copy=GC.AllocateVector(a.vtable,a.Length);
                    } else {
                        copy=GC.AllocateArray(a.vtable,a.Rank,a.Length);
                    }
                } else if (obj is String) {
                    String s=(String)obj;
                    // REVIEW: this is not nice.
                    copy=GC.AllocateString(s.ArrayLength-1);
                } else {
                    copy=GC.AllocateObject(obj.vtable);
                }
                
                VTable.Assert(ObjectLayout.Sizeof(copy)
                              == ObjectLayout.Sizeof(obj),
                              "Copy is not same size as original");
                
                spaceOverhead+=ObjectLayout.Sizeof(copy);
                
                bool first=!CoCoBarrier.instance.AnyTaggedForCopying;
                UIntPtr thisSpaceOverhead;
                if (CoCoBarrier.instance.TagObjectForCopy(obj,copy,
                                                          out thisSpaceOverhead)) {
                    cnt++;
                    if (first) {
                        lock (interlock) {
                            if (!wantCoCo && !doingCoCo) {
                                wantCoCo=true;
                            }
                        }
                    }
                }
                
                spaceOverhead+=thisSpaceOverhead;
            }
        }
        
        internal class UpdateAndForwardReferenceVisitor: UpdateReferenceVisitor
        {
            internal override UIntPtr ForwardIfNecessary(UIntPtr addr)
            {
                return CoCoBarrier.ToSpaceAsPtr(addr);
            }
        }
        
        internal class TaggingPartialFreePageVisitor: SegregatedFreeList.PartialFreePageVisitor
        {
            UIntPtr cnt;
            UIntPtr unmarkedCnt;
            UIntPtr delayedCnt;
            ulong emptyCnt;
            bool delay;
            
            internal override void Start()
            {
                cnt=UIntPtr.Zero;
                unmarkedCnt=UIntPtr.Zero;
                delayedCnt=UIntPtr.Zero;
                emptyCnt=0;
                if (fDebug) {
                    VTable.DebugPrint("    $$$ delayCnt = ");
                    VTable.DebugPrint((ulong)delayCnt);
                    VTable.DebugPrint(", markingForCoCo = ");
                    VTable.DebugPrint((ulong)markingForCoCo);
                    VTable.DebugPrint("\n");
                }
                if (delayCnt==0) {
                    delay=(markingForCoCo!=0); // delay if there are still pages marked
                } else {
                    delayCnt--;
                    delay=true;
                }
                if (fDebug) {
                    VTable.DebugPrint("    $$$ delayCnt = ");
                    VTable.DebugPrint((ulong)delayCnt);
                    VTable.DebugPrint(", markingForCoCo = ");
                    VTable.DebugPrint((ulong)markingForCoCo);
                    VTable.DebugPrint(", delay = ");
                    VTable.DebugPrint(delay?"yes":"no");
                    VTable.DebugPrint("\n");
                }
            }
            
            internal override void Finish()
            {
                lastSmallPagesRecycle=SegregatedFreeList.SmallPages;
                if (fDebug) {
                    VTable.DebugPrint("   $$$ marked ");
                    VTable.DebugPrint((ulong)cnt);
                    VTable.DebugPrint(", unmarked ");
                    VTable.DebugPrint((ulong)unmarkedCnt);
                    VTable.DebugPrint(", delayed ");
                    VTable.DebugPrint((ulong)delayedCnt);
                    VTable.DebugPrint(", and freed ");
                    VTable.DebugPrint(emptyCnt);
                    VTable.DebugPrint(".\n");
                }
                if (cnt!=0) {
                    delayCnt=cocoDelay;
                    markingForCoCo=1;
#if !ARM && !ISA_ARM
                    // HACK: MemoryBarrier is unimplemented in ARM 
                    // and causes compile-time failures when building
                    // mscorlib in sepcomp mode. This change will break
                    // CoCo if built with ARM.
                    Thread.MemoryBarrier();
#endif
                }
            }
            
            internal override void ObserveEmptyPage()
            {
                emptyCnt++;
            }
            
            internal override unsafe SegregatedFreeList.PartialPageAction
            VisitPage(UIntPtr page,
                      SegregatedFreeList.PageHeader *ph,
                      int cells)
            {
                if (fDebugPage) {
                    VTable.DebugPrint("      $$ visiting page.\n");
                }
                CoCoPageUserValue v=new CoCoPageUserValue(ph->userValue);
                if (inFixUp && v.Marked) {
                    unmarkedCnt++;
                    v.Marked=false;
                    if (v.Pinned) {
                        v.Pinned=false;
                        v.Version=pinPenalty; /* use the Version to delay
                                                 any future evacuation
                                                 attempts for this page */
                    }
                } else if (!doingCoCo && !delay) {
                    if (v.Version>=1) {
                        // this page has a non-zero Version - this means
                        // that any attempts to evacuate it should be delayed.
                        v.Version--;
                        delayedCnt++;
                        if (fDebugPage) {
                            VTable.DebugPrint("      $$ page had non-zero version.\n");
                        }
                    } else {
                        if (fDebugPage) {
                            VTable.DebugPrint("      $$ cnt = ");
                            VTable.DebugPrint((ulong)cnt);
                            VTable.DebugPrint(", lastSmallPagesRecycle = ");
                            VTable.DebugPrint((ulong)lastSmallPagesRecycle);
                            VTable.DebugPrint(", sizeFracLim = ");
                            VTable.DebugPrint((ulong)sizeFracLim);
                            VTable.DebugPrint(", sizeLim = ");
                            VTable.DebugPrint((ulong)sizeLim);
                            VTable.DebugPrint(", PageSize = ");
                            VTable.DebugPrint((ulong)PageTable.PageSize);
                            VTable.DebugPrint(", freeCount = ");
                            VTable.DebugPrint((ulong)ph->freeCount);
                            VTable.DebugPrint(", pageFragThres = ");
                            VTable.DebugPrint((ulong)pageFragThres);
                            VTable.DebugPrint(", cells = ");
                            VTable.DebugPrint((ulong)cells);
                            VTable.DebugPrint("\n");
                        }
                        if ((long)cnt < ((long)lastSmallPagesRecycle
                                         /(long)sizeFracLim)
                            && (sizeLim<0 ||
                                cnt*PageTable.PageSize < (UIntPtr)sizeLim)
                            && ph->freeCount*pageFragThres >= cells) {
                            cnt++;
                            v.Marked=true;
                        }
                    }
                } else {
                    if (fDebugPage) {
                        VTable.DebugPrint("      $$ not doing anything about page.\n");
                    }
                }
                ph->userValue=v.Bits;
                if (v.Marked) {
                    return SegregatedFreeList.PartialPageAction.CommitFull;
                } else {
                    return SegregatedFreeList.PartialPageAction.CommitFree;
                }
            }
        }
        
        internal class StackForwardReferenceVisitor : ConcurrentMSCollector.StackMarkReferenceVisitor
        {
            internal override unsafe void ProcessObjectPtr(UIntPtr realPtr,
                                                           UIntPtr *loc,
                                                           UIntPtr addr)
            {
                UIntPtr forward=CoCoBarrier.ToSpaceAsPtr(realPtr);
                if (forward!=realPtr) {
                    *loc=addr-realPtr+forward;
                }
                markReferenceVisitor.VisitValueAnyThreadMaybeNull(forward);
            }
        }

        internal class StackNopReferenceVisitor : NonNullReferenceVisitor
        {
            [Inline]
            internal override unsafe void Visit(UIntPtr *location)
            {
                // do nothing
            }
        }

        internal class StackMarkPinnedReferenceVisitor : ConcurrentMSCollector.StackMarkReferenceVisitor
        {
            internal override unsafe void ProcessObjectPtr(UIntPtr realPtr,
                                                           UIntPtr *loc,
                                                           UIntPtr addr)
            {
                // FIXME: DoPin() already does FindObjectForInteriorPtr
                CoCoBarrier.instance.DoPin(realPtr,CoCoBarrier.Pinner.StackScan);
            }
        }

        private static ulong cyclesStarted;
        private static ulong cycles;
        
        private static bool fVerbose { get { return false; } }
        private static bool fDebug { get { return false; } }
        private static bool fDebugPage { get { return false; } }
    }

}

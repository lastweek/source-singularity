////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:  GCTracing.cs
//
//  Note:  Provides logging facilities for the garbage collector.
//  This is intended to be used in both kernel and SIPs, SIPs
//  will get a private memory buffer for these entries, separated from the kernel log
//

using System;
using System.Diagnostics;
using System.Text;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Isal;
using System.GCs;
using System.Collections;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.V1.Services;    
using Microsoft.Singularity.Eventing;    


namespace Microsoft.Singularity
{
    [CLSCompliant(false)]
    [AccessedByRuntime("output to header - methods defined in GCTracing.cpp")]
    public class GCProfilerLogger : GCProfiler
    {

        [CLSCompliant(false)]
        public class GCTypeSource : EventSource {


            public static GCTypeSource Create(string sourceName, uint typeSize, ulong options) {
                uint qos = QualityOfService.PermanentEvents;
                if (options != 0) {
                    qos |= QualityOfService.OOM_BreakOnRecycle;
                }

                EventingStorage storage = EventingStorage.CreateLocalStorage(qos, typeSize);

                if (storage == null) {

                    return null;                                                  
                }
                
                GCTypeSource Logger  = new GCTypeSource(sourceName, 
                                                        storage,
                                                        ENABLE_ALL_MASK);

                if (Logger != null) {

                    Logger.Register();
                }

                return Logger;
            }

            GCTypeSource(string sourceName, EventingStorage storage, uint controlFlags) 
                :base(sourceName, storage, controlFlags) {}
          
        }

        [CLSCompliant(false)]
        public class GCEventSource : EventSource {


            public static GCEventSource Create(string sourceName, uint typeSize, ulong options) {
                uint qos = QualityOfService.RecyclableEvents;
                if (options != 0) {
                    qos |= QualityOfService.OOM_BreakOnRecycle;
                }

                EventingStorage storage = EventingStorage.CreateLocalStorage(qos, typeSize);

                if (storage == null) {

                    return null;                                                  
                }
                
                GCEventSource Logger  = new GCEventSource(sourceName, 
                                                          storage,
                                                          ENABLE_ALL_MASK);

                if (Logger != null) {

                    Logger.Register();
                }

                return Logger;
            }

            GCEventSource(string sourceName, EventingStorage storage, uint controlFlags) 
                :base(sourceName, storage, controlFlags) {}
          
        }

        
        [CLSCompliant(false)]
        [AccessedByRuntime("output to header - methods defined in GCTracing.cpp")]
        public class ProfilerBuffer
        {
            
            private const int   cycleGranularity = 5000000;
            public Thread       OwningThread;
            private ulong       lastCycle;
            private ulong       firstCycle;

#if LEGACY_GCTRACING

            [AccessedByRuntime("output to header : defined in GCTracing.cpp")]
            [MethodImpl(MethodImplOptions.InternalCall)]
            [StackBound(256)]
            [NoHeapAllocation]
            public static extern unsafe void SetupBuffer(byte * memoryBuffer, ulong bufferSize);

#endif  //  LEGACY_GCTRACING

            //
            //  ABI entries
            //

            [AccessedByRuntime("output to header : defined in GCTracing.cpp")]
            [MethodImpl(MethodImplOptions.InternalCall)]
            [StackBound(256)]
            [NoHeapAllocation]
            public static extern unsafe void LogGenerations(int maxGeneration, int * generations);

            [AccessedByRuntime("output to header : defined in GCTracing.cpp")]
            [MethodImpl(MethodImplOptions.InternalCall)]
            [StackBound(256)]
            [NoHeapAllocation]
            public static extern unsafe void LogInterval(ulong Delta);
            
            [AccessedByRuntime("output to header : defined in GCTracing.cpp")]
            [MethodImpl(MethodImplOptions.InternalCall)]
            [StackBound(256)]
            [NoHeapAllocation]
            public static extern unsafe void LogAllocation(int threadId, UIntPtr objectAddress, uint stkNo);
            
            [AccessedByRuntime("output to header : defined in GCTracing.cpp")]
            [MethodImpl(MethodImplOptions.InternalCall)]
            [StackBound(256)]
            [NoHeapAllocation]
            public static extern unsafe void LogObject(uint ArraySize, UIntPtr * objectParameters);

            [AccessedByRuntime("output to header : defined in GCTracing.cpp")]
            [MethodImpl(MethodImplOptions.InternalCall)]
            [StackBound(256)]
            [NoHeapAllocation]
            public static extern unsafe void LogRoots(uint ArraySize, UIntPtr * objectRoots);

            [AccessedByRuntime("output to header : defined in GCTracing.cpp")]
            [MethodImpl(MethodImplOptions.InternalCall)]
            [StackBound(256)]
            [NoHeapAllocation]
            public static extern unsafe void LogType(uint typeId, string typeName); 
            
            [AccessedByRuntime("output to header : defined in GCTracing.cpp")]
            [MethodImpl(MethodImplOptions.InternalCall)]
            [StackBound(256)]
            [NoHeapAllocation]
            public static extern unsafe void LogStack(uint stackNo, uint typeNo, UIntPtr size, uint stackSize, uint * funcIDs); // 'n'
            
            [AccessedByRuntime("output to header : defined in GCTracing.cpp")]
            [MethodImpl(MethodImplOptions.InternalCall)]
            [StackBound(256)]
            [NoHeapAllocation]
            public static extern unsafe void LogFunction(uint funcNo, UIntPtr eip);
            
            public ProfilerBuffer()
            {
                firstCycle = Processor.CycleCount;
            }
            
            //
            //  Local definitions
            //

            public void LogTick() {
                
                //  Log an entry describing the delta in cycles

                ulong nowCycle = Processor.CycleCount;

                // Emit a tick-count record only if it's been a while since the last one.
                if (nowCycle > lastCycle + cycleGranularity) {

                    lastCycle = nowCycle;
                    ProfilerBuffer.LogInterval((ulong) ((lastCycle - firstCycle) / 1000000));
                }
            }
        }

        //
        //  Local variables
        //
        
        private const int   maxGeneration = 3;        // CLR Profiler only handles this many
        private int[]       generations;
        ProfilerBuffer      Buffer;

        private Hashtable   typeTable;                // hash of types->ids
        private uint        nextTypeNo;               // hand out IDs monotonically

        private Hashtable   stackTable;               // hash of stacks->ids
        private uint        nextStackNo;
        private const int   stackSize = 16;           // increase for bigger / slower stack traces
        private UIntPtr[]   stackEips;
        private uint[]      stackNos;

        private Hashtable   funcTable;                // hash of Eips->ids
        private uint        nextFuncNo;
        private uint[]      functionsIDs;

        private Thread      recurseThread;            // prevent recursion when the profiler allocates
        private SpinLock    allocationLock;
        
        private bool        enabled;                  // profiling is enabled?
        
        private ulong       options;   

        private const uint  tempBufferSize = 1024;   
        private UIntPtr[]   tempGCBuffer;
        private uint        tempGCBufferEntries;

 #if LEGACY_GCTRACING
        private ulong       bufferSize;   
        private static unsafe byte * bufferMemory;

#else  // LEGACY_GCTRACING

        private GCTypeSource typeSource;
        private GCEventSource EventSource;

        [AccessedByRuntime("referenced from Monitoring.cpp")]
        private static unsafe UIntPtr TypeStorageHandle = 0;
        [AccessedByRuntime("referenced from Monitoring.cpp")]
        private static unsafe UIntPtr StorageHandle = 0;

#endif  //  LEGACY_GCTRACING
       
        
        internal GCProfilerLogger()
        {
#if SINGULARITY_KERNEL
            // Initialize spinlock
            allocationLock = new SpinLock(SpinLock.Types.GCTracing);
#endif
        }

        internal static GCProfilerLogger CurrentProfiler = null;

        // The public API for a typical client app.
        static public void StartProfiling()
        {
            //  Query the diagnosis service whether the GC profiling is enabled
            //  This allows setting from the kernel debugger the buffer sizes
            //  for both kernel and SIP profiling. 
            //  Note, these are controlled independently, the implementation
            //  of GCProfileSettings is different between kernel and SIP

            if (CurrentProfiler != null) {

                //
                //  The profiler has been set already. No second attempt is allowed
                //
                
                return;
            }
            
            unsafe{

                int result;
                ulong defaultMemorySize = 0;
                ulong Options = 0;

                result = DiagnosisService.GCProfileSettingsImpl(
                    out defaultMemorySize,
                    out Options
                    );

                if ((result == 0) && (defaultMemorySize > 0)) {
                    
                    CurrentProfiler = new GCProfilerLogger();
                    CurrentProfiler.Initialize(defaultMemorySize, Options);
                    GC.SetProfiler(CurrentProfiler);
                    DebugStub.WriteLine("GC Profiling started");
                }
            }
        }
        
        // Initialization, prior to attempting to set this profiler into the GC.  It's
        // inappropriate to do this stuff inside a constructor.
        internal void Initialize(ulong Size, ulong Flags)
        {
            options = Flags;
            typeTable = new Hashtable();
            stackTable = new Hashtable();
            funcTable = new Hashtable();
            stackEips = new UIntPtr[stackSize];
            stackNos = new uint[stackSize];
            generations = new int[maxGeneration];
            functionsIDs = new uint[stackSize];
            Buffer = new ProfilerBuffer();
            tempGCBuffer = new UIntPtr[tempBufferSize]; 
            tempGCBufferEntries = 0;
#if LEGACY_GCTRACING

            bufferSize = Size;   
            unsafe{

                //  Allocate the memory indicated as parameter, as nonGC

#if SINGULARITY_KERNEL
                UIntPtr pages = Microsoft.Singularity.Memory.MemoryManager.PagesFromBytes(bufferSize);
                bufferMemory = (byte *)Microsoft.Singularity.Memory.MemoryManager.KernelAllocate(
                    pages, null, 0, System.GCs.PageType.NonGC).ToPointer();
#else  // !SINGULARITY_KERNEL
        
                bufferMemory = (byte *)PageTableService.Allocate(bufferSize);

#endif  //SINGULARITY_KERNEL

                if (bufferMemory != null) {

                    // When we set this, we are no longer single-threaded:
                    ProfilerBuffer.SetupBuffer(bufferMemory, bufferSize);
                    this.enabled = true;
                }
            }
#else  // LEGACY_GCTRACING

            typeSource = GCTypeSource.Create("GC.TypeDefinitions", (uint)Size, options);
            EventSource = GCEventSource.Create("GC.Events", (uint)Size, options);

            if ((typeSource == null) || (EventSource == null)) {

                typeSource = null;
                EventSource = null;
                this.enabled = false;

            } else {

                TypeStorageHandle = typeSource.Storage.GetHandle();
                StorageHandle = EventSource.Storage.GetHandle();
                this.enabled = true;
            }

#endif // LEGACY_GCTRACING

        }

        // the API by which our base class calls us

        protected override void Shutdown()
        {
            // This is presumed to be called when the process is single-threaded, since
            // the entire GC heap is shutting down.
            if (enabled) {
                enabled = false;
            }
        }
        protected override void PreGC(int generation)
        {
            try {

                // Take ownership of the buffer to prevent mutating threads from
                // interleaving with us.
                
                DebugStub.Assert(Buffer.OwningThread == null);
                Buffer.OwningThread = Thread.CurrentThread;

                Buffer.LogTick();

                if (generation >= maxGeneration) {
                    generation = maxGeneration-1;
                }
                generations[generation]++;

                unsafe{
                    fixed (int * ptr = &generations[0]) {
                    
                        ProfilerBuffer.LogGenerations(maxGeneration, ptr);
                    }
                }
            }
            catch (Exception) {
                enabled = false;
                throw;
            }
        }

        // A GC has finished.  The world is in a sane place, except that we might not
        // have started up all the mutator threads if this is a StopTheWorld collection.
        protected override void PostGC()
        {
            try {
                // emit the fact a GC has happened, including the state of the heap.
                // TODO: have another function to log the tick count here to estimate the 
                // time spent in GC too.
                
                Buffer.LogTick();
                
                //  We should have an empty buffer, meaning we completed logging from the
                //  previous operation while entering this code.

                DebugStub.Assert(tempGCBufferEntries == 0);

                ScanRoots();

                unsafe{
                    fixed (UIntPtr * ptr = &tempGCBuffer[0]) {
                    
                        ProfilerBuffer.LogRoots(tempGCBufferEntries, ptr);
                        tempGCBufferEntries = 0;
                    }
                }

                // Write all the reachability graph of the heap
                ScanObjects();

                // Once we have finished writing everything, we can allow mutator threads to
                // share access to the fileBuffer with their own consistent entries.
                DebugStub.Assert(Buffer.OwningThread == Thread.CurrentThread);
                Buffer.OwningThread = null;
            }
            catch (Exception) {
                enabled = false;
                throw;
            }
        }

        // In the list of roots, we have found another object
        protected override void ScanOneRoot(UIntPtr objectAddress)
        {
            if (objectAddress != 0) {

                //
                //  If we filled in the temporary buffer, log it and resume
                //  from the beginning. 
                if (tempGCBufferEntries >= tempBufferSize) {
                    
                    unsafe {

                        fixed (UIntPtr * ptr = &tempGCBuffer[0]) {
                        
                            ProfilerBuffer.LogRoots(tempGCBufferEntries, ptr);
                            tempGCBufferEntries = 0;
                        }
                    }
                }
                tempGCBuffer[ tempGCBufferEntries++ ] = (UIntPtr)objectAddress;
            }
        }

        // In the heap reachability graph, we are starting to dump a new object
        protected override void StartScanOneObject(UIntPtr objectAddress, Type type, UIntPtr size)
        {

            DebugStub.Assert(tempGCBufferEntries == 0);
            
            tempGCBuffer[ tempGCBufferEntries++ ] = (UIntPtr)objectAddress;
            tempGCBuffer[ tempGCBufferEntries++ ] = (UIntPtr)GetTypeId(type);
            tempGCBuffer[ tempGCBufferEntries++ ] = (UIntPtr)size;
        }

        // This is one of the references that the current object holds.
        protected override void ScanOneObjectField(UIntPtr objectAddress)
        {
            if ((objectAddress != 0) && (tempGCBufferEntries < tempBufferSize)) {
                
                tempGCBuffer[ tempGCBufferEntries++ ] = (UIntPtr)objectAddress;
            }
        }

        // We are finished scanning one object
        protected override void EndScanOneObject()
        {
            unsafe{
                fixed (UIntPtr * ptr = &tempGCBuffer[0]) {
                
                    ProfilerBuffer.LogObject(tempGCBufferEntries, ptr);
                    tempGCBufferEntries = 0;
                }
            }
        }

        // Create a log entry for the allocation that just occurred on this thread.
        protected override void Allocation(UIntPtr objAddr, Type type, UIntPtr size)
        {
            bool iflag;

            // We cannot recurse inside an Allocation notification, or we will simply
            // blow the stack on the first entry.  Also, we don't want to log allocations
            // that occur as a consequence of logging the state of the GC heap -- though
            // we could support that if we chose to.

            if (enabled &&
                recurseThread != Thread.CurrentThread &&            // recurse?
                Buffer.OwningThread != Thread.CurrentThread) {      // GC logging?

                iflag = Processor.DisableLocalPreemption();
                allocationLock.Acquire();
                
                try {
                    
                    DebugStub.Assert(recurseThread == null);
                    recurseThread = Thread.CurrentThread;
                   
                    Buffer.LogTick();

                    uint stackSize = Isa.GetStackReturnAddresses(stackEips);
                    uint stkNo = 0;

                    if (stackSize > 0) {

                        stkNo = GetStackId(type, size, stackEips, stackSize);
                    }

                    ProfilerBuffer.LogAllocation(Thread.CurrentThread.GetThreadId(), objAddr, stkNo);
                }
                finally {
                    
                    recurseThread = null;
                    allocationLock.Release();
                    Processor.RestoreLocalPreemption(iflag);
                }
            }
        }

        // The rest of our implementation details:

        private uint GetStackId(Type type, UIntPtr size, UIntPtr[] stackEips, uint stackSize)
        {
            // First make sure that we have a type record for the object being
            // instantiated at this stack.

            uint typeNo = GetTypeId(type);

            DebugStub.Assert(stackSize <= stackEips.Length);

            // Then, make sure we have a function record for each Eip in the stack.  Of course
            // we don't know when a bunch of Eips map to different offsets in the same function.
            // So make a function for each unique Eip & fix it up in the post-processing.
            // Hopefully there aren't too many unique callsites in each method.
            
            ulong hash = typeNo; // perhaps "typeNo ^ size" ?
            
            for (int i = 0; i < stackSize; i++) {
                
                // Map the individual Eips into their corresponding functions
                stackNos[i] = GetFunctionId(stackEips[i]);
                hash = (hash << 11) + (hash ^ stackNos[i]);
            }

            // TODO: Note that we will statistically map some distinct stacks into the same
            // stack if they have the same hash.  
            object o = stackTable[hash];
            if (o != null) {
                return (uint) o;
            }

            // It's a novel stack.  Note that we embed the size into the stack, but we
            // don't include the size in the hash.  There's a technique for sharing
            // prefixes of stacks that could be explored here to get more accurate profiles
            // without huge stack expansion.
            // TODO: consider the above.

            uint stackNo = nextStackNo++;

            // Stacks are emitted backwards, presumably to support common prefixes better.
            for (int i = (int)stackSize - 1; i >= 0; i--) {

                functionsIDs[stackSize - 1 - i] = stackNos[i];
            }

            unsafe{
                fixed (uint * ptr = &functionsIDs[0]) {
                
                    ProfilerBuffer.LogStack(stackNo, typeNo, size, stackSize, ptr);
                }
            }
            stackTable[hash] = stackNo;

            return stackNo;
        }

        private uint GetFunctionId(UIntPtr eip)
        {
            // Given the EIP of a Function, make sure the function has been defined.  Since we
            // don't have enough runtime information to map Eips to functions, we must rely on
            // post-processing.
            object o = funcTable[eip];
            if (o != null) {
                return (uint) o;
            }

            uint funcNo = nextFuncNo++;
            ProfilerBuffer.LogFunction(funcNo, eip);
            funcTable[eip] = funcNo;

            return funcNo;
        }

        private uint GetTypeId(Type type)
        {
            // Given a Type, make sure that it has been defined.
            object o = typeTable[type];
            
            if (o != null) {
                return (uint) o;
            }

            uint typeNo = nextTypeNo++;

            // Log this entry before putting it into the hashtable, where other threads might
            // see it.  This means we may have duplicate conflicting entries for the same logical
            // type, but this is tolerated by the profiler.
            
            ProfilerBuffer.LogType(typeNo, type.FullName);

            typeTable[type] = typeNo;
            return typeNo;
        }

    }
}

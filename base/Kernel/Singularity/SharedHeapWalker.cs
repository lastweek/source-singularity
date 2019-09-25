////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   SharedHeapWalker.cs
//
//  Note:
//

using System.Threading;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Channels;

namespace Microsoft.Singularity
{
    internal class SharedHeapWalker
    {
        internal static SharedHeapWalker walker;

        private AutoResetEvent doWalkEvent;
        private unsafe SharedHeap.AllocationOwnerId allocationOwnerId;
        private unsafe SharedHeap.AllocationOwnerId endpointOwnerId;
        private SharedHeap.AllocationMatches match;
        private SharedHeap.AllocationVisitor allocationVisitor;
        private SharedHeap.AllocationVisitor endpointVisitor;

        internal static unsafe void Initialize(
            SharedHeap.AllocationOwnerId allocId,
            SharedHeap.AllocationOwnerId endpointId)
        {
            walker = new SharedHeapWalker(allocId, endpointId);
        }

        private unsafe SharedHeapWalker(
            SharedHeap.AllocationOwnerId allocId,
            SharedHeap.AllocationOwnerId endpointId)
        {
            doWalkEvent = new AutoResetEvent(false);
            allocationOwnerId = allocId;
            endpointOwnerId = endpointId;
            match = new SharedHeap.AllocationMatches(Matches);
            allocationVisitor = new SharedHeap.AllocationVisitor(AllocationVisit);
            endpointVisitor = new SharedHeap.AllocationVisitor(EndpointVisit);
            Thread.CreateThread(Thread.CurrentProcess,
                new ThreadStart(Loop)).Start();
        }

        // Tell the shared heap walker to start a walk at some time in
        // the future.  Multiple calls to DoWalk may be coalesced together,
        // resulting in only a single walk.
        internal void RequestWalk()
        {
            doWalkEvent.Set();
        }

        // Main loop of the shared heap walker.  Walk each node in
        // the shared heap whenever Signal is called.
        //
        // Currently, we signal the walker whenever any process exits,
        // so that one very small process exit can trigger a traversal
        // of a large shared heap.  This raises issues:
        //   - Is this a wise use of resources in the common case?
        //   - Can a malicious small process leverage the large shared heap
        //     to deny service to others?
        // We could avoid these issues by keeping segregated shared
        // heap allocation lists (one list per process), but we feared
        // the common case overhead of maintaining these lists (e.g. locking
        // during Send/Receive).  Furthermore:
        //   - The shared heap is typically not large, and process
        //     exit is infrequent compared to other operations, so the common
        //     case resource usage is not likely to be significant.
        //   - Only one thread walks the heap, so the denial-of-service
        //     potential is small.  At worst, such an attack could:
        //     - Cause the thread below to use some fraction of the CPU time
        //       (a waste of cycles, but not a denial of service)
        //     - Try to increase the size of the shared heap in order to
        //       increase the latency of a shared heap walk (but it's not
        //       clear that well-behaved apps are affected by this latency)
        private void Loop()
        {
            while (true) {
                try {
                    doWalkEvent.WaitOne();
                    Tracing.Log(Tracing.Audit, "Shared heap walk begin");
                    allocationOwnerId.IterateMatchingForModify(
                        match, allocationVisitor);
                    endpointOwnerId.IterateMatchingForModify(
                        match, endpointVisitor);
                    // (Don't visit the endpointPeer list; this gets erased
                    // as part of walking the endpoint list.)
                    Tracing.Log(Tracing.Audit, "Shared heap walk end");
                }
                catch (System.Exception) {
                    Tracing.Log(Tracing.Warning, "Exception thrown in shared heap walker");
                }
            }
        }

        // requires alloc's owner locked
        private unsafe bool Matches(SharedHeap.Allocation* alloc)
        {
            // TODO: using an integer id is only an approximate way to
            // get the right process.  Is this the right design?
            Process process = Process.GetProcessByID(
                SharedHeap.Allocation.GetOwnerProcessId(alloc));
            return process == null;
        }

        // requires alloc's owner unlocked
        private unsafe void AllocationVisit(SharedHeap.Allocation* alloc)
        {
// TODO: support PAGING
#if !PAGING
            SharedHeap.CurrentProcessSharedHeap.Free(alloc, allocationOwnerId);
#endif //PAGING
        }

        // requires alloc's owner unlocked
        private unsafe void EndpointVisit(SharedHeap.Allocation* alloc)
        {
// TODO: support PAGING
#if !PAGING
            EndpointCore* epData = (EndpointCore*)
                // Currently use unchecked access here, since the shared heap
                // walker does not run in the same process as the data.
                SharedHeap.Allocation.GetDataUnchecked(alloc);
            if (!epData->Closed()) {
                epData->Dispose();
            }
            EndpointCore.Free(alloc);
#endif //PAGING
        }
    }
}

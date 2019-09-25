////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ServiceRequestQueue.cs
//
//  Note:
//

using System.Threading;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity
{
    public class ServiceRequestQueue
    {
        // Invariant: head == null <==> tail == null
        // tail.next is undefined.
        private ServiceRequest head = null;
        private ServiceRequest tail = null;
        private SpinLock spinLock;
        private InterruptAwareAutoResetEvent enqueueEvent = new InterruptAwareAutoResetEvent(false);


        ///
        /// <summary>
        ///     Constructor
        /// </summary>
        ///
        public ServiceRequestQueue()
        {
            spinLock = new SpinLock(SpinLock.Types.ServiceQueue);
        }
        
        // Insert an element at the tail of the queue.
        [NoHeapAllocation]
        public void Enqueue(ServiceRequest req)
        {
            // For now disable interrupts:
            bool iflag = Processor.DisableInterrupts();

            spinLock.Acquire();
            try {
                if (head == null) {
                    head = req;
                    tail = req;
                }
                else {
                    tail.next = req;
                    tail = req;
                }
            }
            finally {
                spinLock.Release();
            }

           // Signal an event : for now it is possible that it can be spirous one...
           enqueueEvent.InterruptAwareSet();

           // Reenable interrupts
           Processor.RestoreInterrupts(iflag);
        }

        // Block while the queue is empty, then return the head of the queue.
        public ServiceRequest Dequeue()
        {
            while (true) {

                // For now disable interrupts:
                bool iflag = Processor.DisableInterrupts();

                spinLock.Acquire();
                try {
                    if (tail != null) {
                        ServiceRequest req = head;
                        if (req != tail) {
                            head = req.next;
                        }
                        else {
                            head = null;
                            tail = null;
                        }
                        return req;
                    }
                }
                finally {
                    spinLock.Release();

                    // Reenable interrupts
                    Processor.RestoreInterrupts(iflag);
                }

                // Wait on event
                enqueueEvent.InterruptAwareWaitOne();
            }
        }
    }
}

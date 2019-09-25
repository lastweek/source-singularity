////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ThreadQueue.cs
//
//  Note:
//

// #define DEBUG_SCHEDULER

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;

namespace Microsoft.Singularity.Scheduling
{
    // This class is designed to support queues whose enqueue,
    // dequeue, and remove operations do not allocate memory.
    // This feature is useful when writing code that needs to
    // do such operations with interrupts off.
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from c++")]
    public class ThreadQueue
    {
        private ThreadEntry head;
        private ThreadEntry tail;
        private WaitHandleBase handle;

        public ThreadQueue()
        {
            this.head = null;
            this.tail = null;
            this.handle = null;
        }

        public ThreadQueue(WaitHandleBase handle)
        {
            this.head = null;
            this.tail = null;
            this.handle = handle;
        }

        public WaitHandleBase Handle {
            [NoHeapAllocation]
            get { return handle; }
        }

        public ThreadEntry Head
        {
            [NoHeapAllocation]
            get { return head; }
        }

        [NoHeapAllocation]
        public bool IsEnqueued(ThreadEntry entry)
        {
            return (entry.queue == this);
        }

        [NoHeapAllocation]
        public void EnqueueTail(ThreadEntry entry)
        {
            VTable.Assert(entry.next == null);
            VTable.Assert(entry.prev == null);
            VTable.Assert(entry.queue == null);

            entry.queue = this;
            entry.prev = tail;

            if (tail != null) {
                VTable.Assert(tail.next == null);
                tail.next = entry;
            }
            else {
                VTable.Assert(head == null);
                head = entry;
            }

            tail = entry;
        }

        [NoHeapAllocation]
        public void EnqueueHead(ThreadEntry entry)
        {
            VTable.Assert(entry.next == null);
            VTable.Assert(entry.prev == null);
            VTable.Assert(entry.queue == null);

            entry.queue = this;
            entry.next = head;

            if (head != null) {
                VTable.Assert(head.prev == null);
                head.prev = entry;
            }
            else {
                VTable.Assert(tail == null);
                tail = entry;
            }

            head = entry;
        }

        [NoHeapAllocation]
        public void InsertBefore(ThreadEntry position, ThreadEntry entry)
        {
            if (position == null) {
                EnqueueTail(entry);
            }
            else if (position == head) {
                EnqueueHead(entry);
            }
            else {
                VTable.Assert(head != null);
                VTable.Assert(entry.queue == null);

                entry.queue = this;
                entry.prev = position.prev;
                entry.next = position;
                position.prev = entry;
                entry.prev.next = entry;
            }
        }

        [NoHeapAllocation]
        public Thread DequeueHeadThread()
        {
            ThreadEntry entry = DequeueHead();
            if (entry != null) {
                return entry.Thread;
            }
            return null;
        }

        [NoHeapAllocation]
        public Thread DequeueTailThread()
        {
            ThreadEntry entry = DequeueTail();
            if (entry != null) {
                return entry.Thread;
            }
            return null;
        }

        [NoHeapAllocation]
        public ThreadEntry DequeueHead()
        {
            ThreadEntry entry = head;

            if (entry != null) {
                Remove(entry);
                return entry;
            }
            else {
                return null;
            }
        }

        [NoHeapAllocation]
        public ThreadEntry DequeueTail()
        {
            ThreadEntry entry = tail;

            if (entry != null) {
                Remove(entry);
                return entry;
            }
            else {
                return null;
            }
        }

        [NoHeapAllocation]
        public void DequeueAll(ThreadQueue newParentQueue)
        {

            ThreadEntry threadEntry = head;

            // Navigate through all elements and set the queue to the new queue
            while ( threadEntry != null) {
                threadEntry.queue = newParentQueue;
                threadEntry = threadEntry.next;
            }

            // Move queue elements to parent queue
            if (newParentQueue.tail !=null) {
                // If new parent queue is not empty enqueue new elements at the end of the
                // new parent queue
                newParentQueue.tail.next = this.head;
                newParentQueue.tail = this.tail;
            }
            else  {
                // New queue is empty update head and tail
                newParentQueue.head = this.head;
                newParentQueue.tail = this.tail;
            }

            // Reset initial queue
            this.head = null;
            this.tail = null;

            return;
        }

        [NoHeapAllocation]
        public void Remove(ThreadEntry entry)
        {
            VTable.Assert(entry.queue == this);

            if (entry.next != null) {
                entry.next.prev = entry.prev;
            }
            else {
                VTable.Assert(entry == tail);
                tail = entry.prev;
            }

            if (entry.prev != null) {
                entry.prev.next = entry.next;
            }
            else {
                VTable.Assert(entry == head);
                head = entry.next;
            }

            entry.next = null;
            entry.prev = null;
            entry.queue = null;
        }

        [NoHeapAllocation]
        public bool IsEmpty()
        {
#if false
            Scheduler.AssertDispatchLockHeld();
#endif
            return (head == null);
        }
    }

    // This struct is designed to support queues whose enqueue,
    // dequeue, and remove operations do not allocate memory.
    // This feature is useful when writing code that needs to
    // do such operations with interrupts off.
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from c++")]
    public struct ThreadQueueStruct
    {
        private ThreadEntry head;
        private ThreadEntry tail;

        public ThreadEntry Head
        {
            [NoHeapAllocation]
            get { return head; }
        }

        [NoHeapAllocation]
        public void EnqueueTail(ThreadEntry entry)
        {
            VTable.Assert(entry.next == null);
            VTable.Assert(entry.prev == null);
            VTable.Assert(entry.queue == null);

            entry.prev = this.tail;

            if (tail != null) {
                VTable.Assert(tail.next == null);
                tail.next = entry;
            }
            else {
                VTable.Assert(head == null);
                head = entry;
            }
            tail = entry;
        }

        [NoHeapAllocation]
        public void EnqueueHead(ThreadEntry entry)
        {
            VTable.Assert(entry.next == null);
            VTable.Assert(entry.prev == null);
            VTable.Assert(entry.queue == null);

            entry.next = head;

            if (head != null) {
                VTable.Assert(head.prev == null);
                head.prev = entry;
            }
            else {
                VTable.Assert(tail == null);
                tail = entry;
            }
            head = entry;
        }

        [NoHeapAllocation]
        public ThreadEntry DequeueHead()
        {
            ThreadEntry entry = head;

            if (entry != null) {
                Remove(entry);
                return entry;
            }
            else {
                return null;
            }
        }

        [NoHeapAllocation]
        public ThreadEntry DequeueTail()
        {
            ThreadEntry entry = tail;

            if (entry != null) {
                Remove(entry);
                return entry;
            }
            else {
                return null;
            }
        }

        [NoHeapAllocation]
        public void Remove(ThreadEntry entry)
        {
            if (entry.next != null) {
                entry.next.prev = entry.prev;
            }
            else {
                VTable.Assert(entry == tail);
                tail = entry.prev;
            }

            if (entry.prev != null) {
                entry.prev.next = entry.next;
            }
            else {
                VTable.Assert(entry == head);
                head = entry.next;
            }

            entry.next = null;
            entry.prev = null;
            entry.queue = null;
        }

        [NoHeapAllocation]
        public bool IsEmpty()
        {
            return (head == null);
        }
    }

    ///
    /// <summary>
    /// Class to enumerate thread entries in a queue
    /// </summary>
    ///
    [CLSCompliant(false)]
    public struct ThreadEntryEnum
    {
        ///
        /// <summary>
        /// Constructor
        /// </summary>
        ///
        [NoHeapAllocation]
        public ThreadEntryEnum(ThreadEntry entry)
        {
            this.current = entry;
        }

        ///
        /// <summary>
        /// GetNext element in enumarator
        /// </summary>
        ///
        [NoHeapAllocation]
        public ThreadEntry GetNext()
        {
            ThreadEntry entryToReturn = this.current;

            if (this.current != null) {
                current = current.next;
            }

            return entryToReturn;
        }

        /// <summary> Current element in enumerator</summary>
        private ThreadEntry     current;
    }
}

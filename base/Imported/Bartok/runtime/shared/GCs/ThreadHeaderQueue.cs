//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


#if !SINGULARITY_KERNEL
#define ATOMIC_PUSH
#endif

namespace System.GCs {

    using Microsoft.Bartok.Options;
    using Microsoft.Bartok.Runtime;

    using System;
    using System.Threading;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    /// <summary>
    /// This class defines a queue that is created as a linked list from
    /// each thread object through pointers stored in object headers.
    ///
    /// This queue is used for the concurrent mark sweep collector to allow
    /// it to trace through the heap without ever requiring allocation
    /// or locking.
    ///
    /// Within a thread this is a FIFO queue; all mutations are made at the
    /// head.
    /// </summary>
    internal struct ThreadHeaderQueue {

        [StructLayout(LayoutKind.Sequential)]
        [MixinConditional("ConcurrentMSGC")]
        [Mixin(typeof(PreHeader))]
        [RequiredByBartok]
        internal struct PreHeaderQueue {
            // This use of NoBarriers is just an optimization.  CoCo separately
            // knows that when it is asked to operate on the link field, it
            // should ignore it.  This is accomplished by passing CoCo the
            // offset of this field.  That hackishness is necessary in case we
            // acquire a pointer to this field and operate on it that way.
            [NoBarriers]
            internal UIntPtr link;
        }

        [MixinConditional("ConcurrentMSGC")]
        [Mixin(typeof(Object))]
        internal class ThreadHeaderQueueObject : System.Object {
            internal new PreHeaderQueue preHeader;
        }

        [Inline]
        internal static ThreadHeaderQueueObject MixinObject(Object obj) {
            return (ThreadHeaderQueueObject) obj;
        }

        [MixinConditional("ConcurrentMSGC")]
        [MixinConditional("AllThreadMixins")]
        [Mixin(typeof(Thread))]
        // Should be private, but mixin implementation will warn if visibility
        // does not match that of Thread.
        public sealed class ThreadHeaderQueueThread : Object {
            internal ThreadHeaderQueue gcQueue;
        }

        [Inline]
        internal static ThreadHeaderQueueThread MixinThread(Thread t) {
            return (ThreadHeaderQueueThread) (Object) t;
        }

        /// <summary>
        /// A counter of ongoing attempts to update the queue.  If the
        /// push operations are non-interruptable, the possible values
        /// are 0 and 1.  In the Singularity kernel, the push operation
        /// may be interrupted and code run in the interrupt handlers
        /// may cause overlapping attempts to update the queue, so the
        /// possible values range between 0 and the number of threads.
        /// </summary>
        [NoBarriers]
        private volatile int ongoingUpdates;

        /// <summary>
        /// Contains the pointer to the first object in the queue, or
        /// the TAIL_MARKER value if the queue is empty.
        ///
        /// This field really should be declared volatile, but since C#
        /// does not support atomic operations on volatile variables,
        /// we have to use atomic operations on every read and write of
        /// this variable to ensure is appears to be a volatile variable.
        /// </summary>
        [NoBarriers]
        private UIntPtr head;

        /// <summary>
        /// Contains a pointer to the object that was at the head of the
        /// queue the last time it was 'stolen' by a consuming thread.
        ///
        /// If this.stolenHead is equal to this.head, then there is nothing
        /// on the queue that has not been stolen.  If they are different,
        /// then the queue contains the list of nodes that starts at
        /// this.head and ends at this.stolenHead, but does not include
        /// the node at this.stolenHead.
        ///
        /// This field really should be declared volatile, but since C#
        /// does not support atomic operations on volatile variables,
        /// we have to use atomic operations on every read and write of
        /// this variable to ensure is appears to be a volatile variable.
        /// </summary>
        [NoBarriers]
        private UIntPtr stolenHead;

        /// <summary>
        /// This flag indicates that there has been an attempt to transfer
        /// the contents of a dead thread's ThreadHeaderQueue
        /// to another thread's ThreadHeaderQueue.  The flag is used when
        /// trying to establish that all threads' ThreadHeaderQueues are
        /// empty.  The usage pattern is to first clear this flag, then
        /// iterate through all the threads checking that the
        /// ThreadHeaderQueues are empty, and finally checking that the
        /// flag has not been set during the iteration through the threads.
        /// Doing so prevents an unnoticed transfer of work from an unvisited
        /// dying/dead thread to an already visited thread followed by the
        /// disappearance of the dead thread.
        /// </summary>
        [NoBarriers]
        internal static bool transferAttempt;

        /// <summary>
        /// Every object that is in a ThreadHeaderQueue list must have a
        /// non-zero link field.  To ensure this invariant for the last
        /// element in the list, a non-zero value is used to mark the
        /// end of the list.  TAIL_MARKER is that value.
        /// </summary>
        internal static UIntPtr TAIL_MARKER {
          get { return ~(UIntPtr)3U; }
        }

        /// <summary>
        /// Atomically compare-and-swap (CAS) one value for another.
        /// Return true if the CAS operation succeeds, false otherwise.
        /// </summary>
        private static bool CompareAndSwap(ref UIntPtr variable,
                                           UIntPtr newValue,
                                           UIntPtr comparand)
        {
            return (Interlocked.CompareExchange(ref variable,
                                                newValue,
                                                comparand)
                    == comparand);
        }

        /// <summary>
        /// Reset the queue of a thread.
        /// </summary>
        [Inline]
        internal static void Reset(Thread t) {
            MixinThread(t).gcQueue.Reset();
        }

        /// <summary>
        /// Reset the queue.
        /// </summary>
        [Inline]
        internal void Reset()
        {
            // NOTE: this.head MUST be written to before this.stolenHead!
            Thread.VolatileWrite(ref this.head, TAIL_MARKER);
            Thread.VolatileWrite(ref this.stolenHead, TAIL_MARKER);
            this.ongoingUpdates = 0;
        }

        /// <summary>
        /// Is the queue empty?
        /// </summary>
        internal static bool IsEmpty(Thread t) {
            return MixinThread(t).gcQueue.IsEmpty();
        }

        internal bool IsEmpty() {
            UIntPtr foundHead = Thread.VolatileRead(ref this.head);
            UIntPtr foundStolenHead = Thread.VolatileRead(ref this.stolenHead);
            return (foundHead == foundStolenHead ||
                    foundHead == TAIL_MARKER);
        }

        internal static bool IsReset(Thread thread) {
            return MixinThread(thread).gcQueue.IsReset();
        }

        private bool IsReset() {
            return (Thread.VolatileRead(ref this.head) == TAIL_MARKER &&
                    Thread.VolatileRead(ref this.stolenHead) == TAIL_MARKER);
        }

        /// <summary>
        /// Return the value of an object's link field.
        /// </summary>
        [Inline]
        [DisableNullChecks]
        private static UIntPtr QueueField(Object obj)
        {
            return MixinObject(obj).preHeader.link;
        }

        /// <summary>
        /// Set  an object's link field to a given value.
        /// </summary>
        [Inline]
        [DisableNullChecks]
        [NoBarriers]
        private static void SetQueueField(Object obj, UIntPtr value)
        {
            MixinObject(obj).preHeader.link = value;
        }

        /// <summary>
        /// Perform a CAS operation on an object's link field.
        /// </summary>
        [Inline]
        [DisableNullChecks]
        [NoBarriers]
        private static bool ExchangeQueueField(Object obj,
                                               UIntPtr val,
                                               UIntPtr oldVal)
        {
            ThreadHeaderQueueObject obj2 = MixinObject(obj);
            return CompareAndSwap(ref obj2.preHeader.link, val, oldVal);
        }

        /// <summary>
        /// An object's link field can contain both a link to another
        /// object and two mark bits.  This function returns the link
        /// part of the link field.
        /// </summary>
        [Inline]
        [DisableNullChecks]
        internal static UIntPtr QueueLink(Object obj)
        {
            return QueueField(obj) & ~(UIntPtr)3U;
        }

        /// <summary>
        /// An object's link field can contain both a link to another
        /// object and two mark bits.  This function returns the mark
        /// part of the link field.
        /// </summary>
        [Inline]
        [DisableNullChecks]
        internal static UIntPtr GcMark(Object obj)
        {
            VTable.Assert(obj != null, "Can not get mark of null");
            return (QueueField(obj) & (UIntPtr)3U);
        }

        /// <summary>
        /// Sets the mark value in the header word of the object.
        /// </summary>
        [Inline]
        [DisableNullChecks]
        internal static void SetGcMark(UIntPtr objAddr, UIntPtr markBits)
        {
            SetGcMark(Magic.fromAddress(objAddr), markBits);
        }

        [Inline]
        [DisableNullChecks]
        internal static void SetGcMark(Object obj, UIntPtr markBits)
        {
            SetQueueField(obj, markBits);
        }

        internal static bool IsInQueue(Object obj) {
            return (QueueLink(obj) != UIntPtr.Zero);
        }

        /// <summary>
        /// Link a new value at the head of the queue.  It is assumed that
        /// if the object is unmarked, the value in the header word will
        /// simply be 'unmarkedColor'.  The function returns true if the
        /// object was marked and linked into the queue.  The function
        /// returns false if the object has already linked into an(other)
        /// queue.
        /// </summary>
        [Inline]
        [DisableNullChecks]
        internal static bool Push(Thread t,
                                  UIntPtr objAddr,
                                  UIntPtr markedColor,
                                  UIntPtr unmarkedColor)
        {
            return MixinThread(t).gcQueue.Push(objAddr,
                                               markedColor,
                                               unmarkedColor);
        }

        [Inline]
        [DisableNullChecks]
        [NoBarriers]
        private bool Push(UIntPtr objAddr,
                          UIntPtr markedColor,
                          UIntPtr unmarkedColor)
        {
            VTable.Assert(objAddr != UIntPtr.Zero, "Can not push null!");
            this.ongoingUpdates++;
            UIntPtr oldHead = Thread.VolatileRead(ref this.head);
            Object obj = Magic.fromAddress(objAddr);
            if (ExchangeQueueField(obj,
                                   oldHead + markedColor,
                                   unmarkedColor)) {
#if ATOMIC_PUSH
                Thread.VolatileWrite(ref this.head, objAddr);
#else // ATOMIC_PUSH
                // We took ownership of the object, but since the
                // queue may be updated due to code run in interrupt
                // handlers, we have to use an iterated approach to
                // adding the object to the queue.
                // REVIEW: We don't really need LOCK CMPXCHG, but we do
                // need CMPXCHG (needs to be atomic with respect to the
                // current processor, only).
                UIntPtr foundHead = Interlocked.CompareExchange(ref this.head,
                                                                objAddr,
                                                                oldHead);
                while (foundHead != oldHead) {
                    oldHead = foundHead;
                    SetQueueField(obj, oldHead + markedColor);
                    foundHead = Interlocked.CompareExchange(ref this.head,
                                                            objAddr,
                                                            oldHead);
                }
#endif // ATOMIC_PUSH
                this.ongoingUpdates--;
                return true;
            } else {
                // Someone else enqueued the object
                VTable.Assert(GcMark(obj) == markedColor);
                this.ongoingUpdates--;
                return false;
            }
        }

        /// <summary>
        /// Link a new value at the head of the queue, knowing that the
        /// object is a thread local object.  Since the object is
        /// thread local, we don't need to use a CAS operation to set
        /// the link field of the object.
        /// </summary>
        [Inline]
        [DisableNullChecks]
        internal static void PushPrivateObject(Thread t,
                                               Object obj,
                                               UIntPtr markBits)
        {
            MixinThread(t).gcQueue.PushPrivateObject(obj, markBits);
        }

        [Inline]
        [DisableNullChecks]
        [NoBarriers]
        private void PushPrivateObject(Object obj, UIntPtr markBits)
        {
            VTable.Assert(obj != null, "Can not push null!");
#if ATOMIC_PUSH
            SetQueueField(obj, Thread.VolatileRead(ref this.head) + markBits);
            Thread.VolatileWrite(ref this.head, Magic.addressOf(obj));
#else // ATOMIC_PUSH
            // REVIEW: We don't really need LOCK CMPXCHG, but we do
            // need CMPXCHG (needs to be atomic with respect to the
            // current processor, only).
            UIntPtr oldHead;
            UIntPtr foundHead = Thread.VolatileRead(ref this.head);
            do {
                oldHead = foundHead;
                SetQueueField(obj, oldHead + markBits);
                foundHead = Interlocked.CompareExchange(ref this.head,
                                                        Magic.addressOf(obj),
                                                        oldHead);
            } while (foundHead != oldHead);
#endif // ATOMIC_PUSH
        }

        internal static void DeadThreadNotification(Thread deadThread,
                                                    UIntPtr markedColor)
        {
            StealDead(Thread.CurrentThread, deadThread, markedColor);
        }

        /// <summary>
        /// This method attempts to take values from the passed-in queue
        /// and place it in the 'this' queue.  The method is tolerant
        /// of concurrent attempts to steal from the fromQueue.  The
        /// 'fromThread' is assumed to be dead, which means that no
        /// additions to its queue is possible.
        ///
        /// Rather than reading the old mark value from the header word
        /// of the tail object in the 'fromQueue', the new mark value in
        /// said object is going to be 'markedColor'
        /// </summary>
        [NoBarriers]
        internal static void StealDead(Thread toThread,
                                       Thread fromThread,
                                       UIntPtr markedColor)
        {
            ThreadHeaderQueueThread myToThread = MixinThread(toThread);
            ThreadHeaderQueueThread myFromThread = MixinThread(fromThread);
            myToThread.gcQueue.StealFromDead(ref myFromThread.gcQueue,
                                             markedColor);
        }

        [NoBarriers]
        private void StealFromDead(ref ThreadHeaderQueue fromQueue,
                                   UIntPtr markedColor)
        {
            // It is assumed that there are no concurrent accesses to
            // fromQueue.  The thread owning the queue is supposed to
            // be dead, and there should only be one other thread
            // trying to steal the dead thread's queue.
            if (Thread.VolatileRead(ref fromQueue.head) !=
                Thread.VolatileRead(ref fromQueue.stolenHead)) {
                UIntPtr fromHead, fromTail;
                this.ongoingUpdates++;
                ThreadHeaderQueue.transferAttempt = true;
                if (fromQueue.StealList(out fromHead, out fromTail)) {
                    // Prepend the stolen list segment to our list
                    Object tailObject = Magic.fromAddress(fromTail);
#if ATOMIC_PUSH
                    // NOTE: We don't try to be thread-safe on this.head
                    VTable.Assert(GcMark(tailObject) == markedColor);
                    SetQueueField(tailObject, this.head + markedColor);
                    Thread.VolatileWrite(ref this.head, fromHead);
#else // ATOMIC_PUSH
                    // REVIEW: We don't really need LOCK CMPXCHG, but
                    // we do need CMPXCHG (needs to be atomic with
                    // respect to the current processor, only).
                    UIntPtr oldHead;
                    UIntPtr foundHead = Thread.VolatileRead(ref this.head);
                    do {
                        oldHead = foundHead;
                        SetQueueField(tailObject, oldHead + markedColor);
                        foundHead = Interlocked.CompareExchange(ref this.head,
                                                                fromHead,
                                                                oldHead);
                    } while (foundHead != oldHead);
#endif // ATOMIC_PUSH
                }
                this.ongoingUpdates--;
            }
        }

        [NoBarriers]
        private bool StealList(out UIntPtr outStolenHead,
                               out UIntPtr outStolenTail)
        {
            while (true) {
                UIntPtr thisStolen = Thread.VolatileRead(ref this.stolenHead);
                UIntPtr thisHead = Thread.VolatileRead(ref this.head);
                while (thisStolen != thisHead) {
                    if (thisHead==TAIL_MARKER && thisStolen==UIntPtr.Zero) {
                        // A new thread has been created, and we caught the
                        // thread partway through ThreadHeaderQueue.Reset.
                        break;
                    }
                    VTable.Assert(thisHead != TAIL_MARKER, "thisHead should not be TAIL_MARKER if it is not equal to stolenHead");
                    if (CompareAndSwap(ref this.stolenHead,
                                       thisHead,
                                       thisStolen)) {
                        // We managed to steal part of the list.
                        // Find the end of the stolen list segment.
                        outStolenHead = thisHead;
                        Object obj = Magic.fromAddress(thisHead);
                        UIntPtr next = QueueLink(obj);
                        while (next != thisStolen) {
                            obj = Magic.fromAddress(next);
                            next = QueueLink(obj);
                        }
                        outStolenTail = Magic.addressOf(obj);
                        return true;
                    }
                    thisStolen = Thread.VolatileRead(ref this.stolenHead);
                    thisHead = Thread.VolatileRead(ref this.head);
                }
                if (this.ongoingUpdates == 0 &&
                    Thread.VolatileRead(ref this.stolenHead) ==
                    Thread.VolatileRead(ref this.head)) {
                    // There is nothing to steal.
                    outStolenHead = UIntPtr.Zero;
                    outStolenTail = UIntPtr.Zero;
                    return false;
                }
                // Someone must be in the process of inserting something
                // into the queue (or stealing something from it).
                Thread.Yield();
            }
        }

        internal struct LocalList {

        
            private UIntPtr head;

            /// <summary>
            /// Is the queue empty?
            /// </summary>
            internal bool IsEmpty() {
                return this.head == UIntPtr.Zero;
            }

            /// <summary>
            /// This method attempts to take values from the passed-in queue
            /// and place it in the 'this' local queue.  It assumes that the
            /// 'this' local queue is not concurrently added to.  However,
            /// the method is tolerant of concurrent attempts to steal from
            /// the fromQueue.
            ///
            /// If any values are stolen the method returns true.
            /// </summary>
            [NoBarriers]
            internal bool StealFrom(Thread fromThread, UIntPtr markedColor)
            {
                ThreadHeaderQueueThread myFromThread = MixinThread(fromThread);
                return this.StealFrom(ref myFromThread.gcQueue, markedColor);
            }

            [NoBarriers]
            private bool StealFrom(ref ThreadHeaderQueue fromQueue,
                                   UIntPtr markedColor)
            {
                UIntPtr fromHead, fromTail;
                if (fromQueue.StealList(out fromHead, out fromTail)) {
                    // Prepend the stolen list segment to our list
                    Object tailObject = Magic.fromAddress(fromTail);
                    VTable.Assert(ThreadHeaderQueue.GcMark(tailObject) ==
                                  markedColor);
                    SetQueueField(tailObject, this.head + markedColor);
                    this.head = fromHead;
                    return true;
                } else {
                    return false;
                }
            }

            /// <summary>
            /// Unlink a value from the head of the queue. This
            /// method is NOT thread safe.  The method is supposed to be
            /// called only by the thread that populates the queue.
            /// </summary>
            [Inline]
            [DisableNullChecks]
            internal Object Pop(UIntPtr markedColor)
            {
                VTable.Assert(!this.IsEmpty(), "Queue is empty!");
                Object obj = Magic.fromAddress(this.head);
                VTable.Assert(ThreadHeaderQueue.GcMark(obj) == markedColor);
                UIntPtr newHead = QueueLink(obj);
                this.head = newHead;
                SetQueueField(obj, markedColor);
                return obj;
            }

        }

    }

}

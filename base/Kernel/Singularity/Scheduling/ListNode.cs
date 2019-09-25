////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ListNode.cs
//
//  Note:
//

using System;
using System.Threading;

namespace Microsoft.Singularity.Scheduling
{
    /// <summary>
    /// Summary description for ListNode.
    /// </summary>

    [CLSCompliant(false)]
    public class ListNode
    {
        public ListNode Previous;   // Before this node
        public ListNode Next;       // After this node
        public Thread   Data;

        public ListNode()
        {
            Previous = null;
            Next = null;
        }

        [CLSCompliant(false)]
        public ListNode(Thread dataref)
        {
            Previous = null;
            Next = null;
            Data = dataref;
        }

        // DI -- safe
        public ListNode ListRemove()
        {
            ListNode next;

            if ((next = Next) == this)
                return null;

            next.Previous = Previous;
            Previous.Next = next;
            Previous = Next = this;
            return next;
        }

        // DI -- safe
        public ListNode InsertIntoList(ListNode list)
        {
            if (list == null) {
                Next = Previous = this;
            }
            else {
                Next = list.Next;
                Next.Previous = this;
                list.Next = this;
                Previous = list;
            }
            return this;
        }

    }
}

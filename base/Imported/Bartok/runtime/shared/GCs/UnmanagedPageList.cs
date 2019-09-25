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

    using System.Runtime.CompilerServices;

    internal unsafe struct UnmanagedPageList {

        internal static UnmanagedPageList pageCache;

        private UIntPtr head;
        private UIntPtr tail;

        internal static void ReleaseStandbyPages() {
            while (!pageCache.IsEmpty) {
                UIntPtr pageAddr = pageCache.RemoveHead();
                PageManager.ReleaseUnusedPages(PageTable.Page(pageAddr),
                                               (UIntPtr) 1, false);
            }
        }

        internal bool IsEmpty {
            [Inline]
                get { return this.head == UIntPtr.Zero; }
        }

        internal bool IsSingleton {
            [Inline]
                get { return this.head == this.tail; }
        }

        internal UIntPtr Head {
            get { return this.head; }
        }

        internal UIntPtr Tail {
            get { return this.tail; }
        }

        internal void AddTail(UIntPtr pageAddr) {
            if (this.head == UIntPtr.Zero) {
                this.head = pageAddr;
            } else {
                SetNext(this.tail, pageAddr);
            }
            this.tail = pageAddr;
        }

        internal void AddHead(UIntPtr pageAddr) {
            SetNext(pageAddr, this.head);
            this.head = pageAddr;
            if (this.tail == UIntPtr.Zero) {
                this.tail = pageAddr;
            }
        }

        internal UIntPtr RemoveHead() {
            UIntPtr oldHead = this.head;
            UIntPtr newHead = Next(oldHead);
            this.head = newHead;
            if (newHead == UIntPtr.Zero) {
                this.tail = UIntPtr.Zero;
            }
            SetNext(oldHead, UIntPtr.Zero);
            return oldHead;
        }

        [Inline]
        private static UIntPtr Next(UIntPtr pageAddr) {
            return *(UIntPtr *) pageAddr;
        }

        [Inline]
        private static void SetNext(UIntPtr pageAddr,
                                           UIntPtr nextPageAddr)
        {
            *(UIntPtr *) pageAddr = nextPageAddr;
        }

        internal static UIntPtr* FirstPageAddr(UIntPtr pageAddr) {
            return (((UIntPtr *) pageAddr) + 1);
        }

        internal static UIntPtr* EndPageAddr(UIntPtr pageAddr) {
            return (UIntPtr *) (pageAddr + PageTable.PageSize);
        }

        internal struct Enumerator {

            private bool movedToFirst;
            private UIntPtr currentPage;
            private UIntPtr tailPage;

            internal Enumerator(ref UnmanagedPageList pageList) {
                this.movedToFirst = false;
                this.currentPage = pageList.Head;
                this.tailPage = pageList.Tail;
            }

            internal bool MoveNext() {
                if (!this.movedToFirst) {
                    this.movedToFirst = true;
                    return (this.currentPage != UIntPtr.Zero);
                } else if (currentPage == tailPage) {
                    return false;
                } else {
                    this.currentPage = Next(this.currentPage);
                    VTable.Assert(this.currentPage != UIntPtr.Zero);
                    return true;
                }
            }

            internal UIntPtr Current {
                get { return this.currentPage; }
            }

        }

    }

}


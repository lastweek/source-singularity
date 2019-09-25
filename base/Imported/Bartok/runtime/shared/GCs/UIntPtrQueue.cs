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
  using System.Threading;

  internal unsafe struct UIntPtrQueue {

      private UnmanagedPageList pageList;
      private UIntPtr readPage;
      private PageCursor readCursor;
      private PageCursor writeCursor;

      internal bool IsEmpty {
          [Inline]
          get { return (this.readCursor.cursor == this.writeCursor.cursor); }
      }

      internal void Write(UIntPtr value) {
          if (this.writeCursor.IsEmpty) {
              this.AdvanceWritePage();
          }
          if (this.readCursor.limit == this.writeCursor.cursor) {
              this.writeCursor.Write(value);
              this.readCursor.limit = this.writeCursor.cursor;
          } else {
              this.writeCursor.Write(value);
          }
      }

      internal void Write(UIntPtr value1, UIntPtr value2) {
          if (this.writeCursor.HasTwo) {
              if (this.readCursor.limit == this.writeCursor.cursor) {
                  this.writeCursor.Write(value1);
                  this.writeCursor.Write(value2);
                  this.readCursor.limit = this.writeCursor.cursor;
              } else {
                  this.writeCursor.Write(value1);
                  this.writeCursor.Write(value2);
              }
          } else {
              this.Write(value1);
              this.Write(value2);
          }
      }

      internal UIntPtr Read() {
          if (this.readCursor.IsEmpty) {
              this.AdvanceReadPage();
          }
          return this.readCursor.Read();
      }

      internal UIntPtr Read(out UIntPtr value2) {
          if (this.readCursor.HasTwo) {
              UIntPtr value1 = this.readCursor.Read();
              value2 = this.readCursor.Read();
              return value1;
          } else {
              UIntPtr value1 = this.Read();
              value2 = this.Read();
              return value1;
          }
      }

      internal void Cleanup(bool mustBeEmpty) {
          if (mustBeEmpty) {
              VTable.Assert(this.pageList.Head == this.pageList.Tail);
              VTable.Assert(this.readCursor.cursor == this.writeCursor.cursor);
          }
          if (this.readPage != UIntPtr.Zero) {
              UnmanagedPageList.pageCache.AddHead(this.readPage);
              this.readPage = UIntPtr.Zero;
          }
          while (!this.pageList.IsEmpty) {
              UIntPtr headPage = this.pageList.RemoveHead();
              UnmanagedPageList.pageCache.AddHead(headPage);
          }
          this.writeCursor = new PageCursor(null, null);
          this.readCursor = new PageCursor(null, null);
      }

      private void AdvanceReadPage() {
          if (this.pageList.IsEmpty) {
              return;
          }
          if (this.readPage != UIntPtr.Zero) {
              UnmanagedPageList.pageCache.AddHead(this.readPage);
          }
          this.readPage = this.pageList.RemoveHead();
          UIntPtr* startPtr = UnmanagedPageList.FirstPageAddr(this.readPage);
          UIntPtr* limitPtr;
          if (this.pageList.IsEmpty) {
              limitPtr = this.writeCursor.cursor;
          } else {
              limitPtr = UnmanagedPageList.EndPageAddr(this.readPage);
          }
          this.readCursor = new PageCursor(startPtr, limitPtr);
      }

      private void AdvanceWritePage() {
          UIntPtr pageAddr;
          if (UnmanagedPageList.pageCache.IsEmpty) {
              bool fCleanPages = true;
              UIntPtr page = PageManager.EnsurePages(null, (UIntPtr) 1,
                                                     PageType.System,
                                                     ref fCleanPages);
              pageAddr = PageTable.PageAddr(page);
          } else {
              pageAddr = UnmanagedPageList.pageCache.RemoveHead();
          }
          this.pageList.AddTail(pageAddr);
          this.writeCursor =
              new PageCursor(UnmanagedPageList.FirstPageAddr(pageAddr),
                             UnmanagedPageList.EndPageAddr(pageAddr));
      }

      private struct PageCursor {
          internal UIntPtr *cursor;
          internal UIntPtr *limit;

          internal PageCursor(UIntPtr *start, UIntPtr *limit) {
              this.cursor = start;
              this.limit = limit;
          }

          internal bool IsEmpty {
              [Inline]
              get { return this.cursor == this.limit; }
          }

          internal bool HasTwo {
              [Inline]
              get { return (this.cursor + 2 <= this.limit); }
          }

          [Inline]
          internal void Write(UIntPtr value) {
              VTable.Deny(this.IsEmpty);
              *this.cursor++ = value;
          }

          [Inline]
          internal UIntPtr Read() {
              VTable.Deny(this.IsEmpty);
              return *this.cursor++;
          }

          internal bool MoveNext() {
              if (this.IsEmpty) {
                  return false;
              }
              this.cursor++;
              return (!this.IsEmpty);
          }

          internal UIntPtr Current {
              get { return *this.cursor; }
          }

          internal UIntPtr* CurrentAddr {
              get { return this.cursor; }
          }

      }

      internal unsafe struct Enumerator {

          private UnmanagedPageList.Enumerator pageEnumerator;
          private UIntPtr lastPageStart;
          private UIntPtr* lastPageLimit;
          private PageCursor currentCursor;

          internal Enumerator(ref UIntPtrQueue queue) {
              this.pageEnumerator =
                  new UnmanagedPageList.Enumerator(ref queue.pageList);
              this.lastPageLimit = queue.writeCursor.cursor;
              this.lastPageStart =
                  PageTable.PageAlign((UIntPtr) lastPageLimit);
              this.currentCursor = new PageCursor(null, null);
              if (this.pageEnumerator.MoveNext()) {
                  UIntPtr currentPage = this.pageEnumerator.Current;
                  this.SetCursor(currentPage);
              }
          }

          private void SetCursor(UIntPtr pageAddr) {
              UIntPtr* preFirstAddr =
                  UnmanagedPageList.FirstPageAddr(pageAddr) - 1;
              if (pageAddr == lastPageStart) {
                  this.currentCursor = new PageCursor(preFirstAddr,
                                                      this.lastPageLimit);
              } else {
                  UIntPtr* endAddr = UnmanagedPageList.EndPageAddr(pageAddr);
                  this.currentCursor = new PageCursor(preFirstAddr, endAddr);
              }
          }

          internal bool MoveNext() {
              if (this.currentCursor.MoveNext()) {
                  return true;
              }
              if (!this.pageEnumerator.MoveNext()) {
                  return false;
              }
              UIntPtr currentPage = this.pageEnumerator.Current;
              this.SetCursor(currentPage);
              return this.currentCursor.MoveNext();
          }

          internal UIntPtr Current {
              get { return this.currentCursor.Current; }
          }

          internal UIntPtr* CurrentAddr {
              get { return this.currentCursor.CurrentAddr; }
          }

          internal void Reset() {
              throw new Exception("No reset on UIntPtrQueue iterator");
          }

      }

  }

}

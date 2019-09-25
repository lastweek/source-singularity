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

  internal unsafe struct UIntPtrStack {

      private UnmanagedPageList pageList;
      private UIntPtr stackPage;
      private UIntPtr *stackBottom;
      private UIntPtr *stackPtr;
      private UIntPtr *stackTop;

      internal bool IsEmpty {
          get {
              return ((this.stackPtr == this.stackBottom) &&
                      this.pageList.IsEmpty);
          }
      }

      [Inline]
      internal void Write(UIntPtr value) {
          if (this.stackPtr == stackTop) {
              AdvancePage();
          }
          *this.stackPtr = value;
          this.stackPtr++;
      }

      [Inline]
      internal void Write(UIntPtr value1, UIntPtr value2) {
          if (this.stackPtr + 2 <= stackTop) {
              *this.stackPtr = value1;
              *(this.stackPtr + 1) = value2;
              this.stackPtr += 2;
          } else {
              this.Write(value1);
              this.Write(value2);
          }
      }

      [Inline]
      internal UIntPtr Read() {
          if (this.stackPtr == stackBottom) {
              RetractPage();
          }
          this.stackPtr--;
          return *this.stackPtr;
      }

      [Inline]
      internal UIntPtr Read(out UIntPtr value2) {
          if (this.stackPtr - 2 >= stackBottom) {
              value2 = *(this.stackPtr - 1);
              UIntPtr value1 = *(this.stackPtr - 2);
              this.stackPtr -= 2;
              return value1;
          } else {
              value2 = this.Read();
              UIntPtr value1 = this.Read();
              return value1;
          }
      }

      internal void Cleanup(bool mustBeEmpty) {
          if (mustBeEmpty) {
              VTable.Assert(this.IsEmpty);
          }
          if  (this.stackPage != UIntPtr.Zero) {
              UnmanagedPageList.pageCache.AddHead(this.stackPage);
              this.stackPage = UIntPtr.Zero;
          }
          while (!this.pageList.IsEmpty) {
              UIntPtr headPage = this.pageList.RemoveHead();
              UnmanagedPageList.pageCache.AddHead(headPage);
          }
          this.stackBottom = null;
          this.stackTop = null;
          this.stackPtr = null;
      }

      private void AdvancePage() {
          if (this.stackPage != UIntPtr.Zero) {
              this.pageList.AddHead(this.stackPage);
          }
          if (UnmanagedPageList.pageCache.IsEmpty) {
              bool fCleanPages = true;
              UIntPtr page = PageManager.EnsurePages(null, (UIntPtr) 1,
                                                     PageType.System,
                                                     ref fCleanPages);
              this.stackPage = PageTable.PageAddr(page);
          } else {
              this.stackPage = UnmanagedPageList.pageCache.RemoveHead();
          }
          this.stackBottom = UnmanagedPageList.FirstPageAddr(this.stackPage);
          this.stackPtr = this.stackBottom;
          this.stackTop = UnmanagedPageList.EndPageAddr(this.stackPage);
      }

      private void RetractPage() {
          UnmanagedPageList.pageCache.AddHead(this.stackPage);
          this.stackPage = this.pageList.RemoveHead();
          this.stackBottom = UnmanagedPageList.FirstPageAddr(this.stackPage);
          this.stackTop = UnmanagedPageList.EndPageAddr(this.stackPage);
          this.stackPtr = this.stackTop;
      }

  }

}

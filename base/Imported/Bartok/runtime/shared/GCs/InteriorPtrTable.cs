//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs {

  using Microsoft.Bartok.Runtime;
  using System.Runtime.CompilerServices;

  internal class InteriorPtrTable {

      // WARNING: don't initialize any static fields in this class
      // without manually running the class constructor at startup!

      internal const uint OFFSET_NO_DATA = 0;
      internal const uint OFFSET_SKEW = 1;

      /* 
       * Returns a pointer to the beginning of an object such that the
       * pointer is less than or equal to addr.  N.B. Before may return a
       * pointer to an alignment or an unused space token.
       */
      private static UIntPtr Before(UIntPtr addr) {
          UIntPtr page = PageTable.Page(addr);
          uint offset = PageTable.Extra(page);
          // OFFSET_NO_DATA and negative offsets should always fail this
          // test.
          if (PageTable.PageAddr(page) + (offset-OFFSET_SKEW) > addr) {
              // If the addr is an interior pointer of an object on a
              // previous page, go back one entry.
              --page;
              offset = PageTable.Extra(page);
          }
          if (offset == OFFSET_NO_DATA) {
              // Scroll back until we find a page entry with real data in
              // it.  This handles the case of a large object allocated
              // across pages.
              do {
                  --page;
                  offset = PageTable.Extra(page);
              }
              while (offset == OFFSET_NO_DATA);
          }
          VTable.Assert(offset > OFFSET_NO_DATA, "No offset data");
          // Unused: since we currently do not use negative offsets in the
          // page table.  This would be more efficient for really big
          // objects, but the OFFSET_NO_DATA value works fine too.
          /*
            // Scroll backwards using big steps.  Offset will never be
            // OFFSET_NO_DATA in this loop.
            while (offset < OFFSET_NO_DATA) {
            entry += (offset - OFFSET_SKEW);
            offset = *entry;
            }
          */
          return PageTable.PageAddr(page) + (offset - OFFSET_SKEW);
      }

      /*
       * Returns a pointer to the first object on the given page.
       * N.B. If called on a page with no ~allocated~ first object it may
       * return a pointer to the unused space token.
       */
      internal static UIntPtr First(UIntPtr page)
      {
          uint offset = PageTable.Extra(page);
          UIntPtr pageAddr = PageTable.PageAddr(page);
          UIntPtr currAddr;
          if (offset != OFFSET_NO_DATA) {
              currAddr = pageAddr + (offset - OFFSET_SKEW);
          } else {
              currAddr = Before(pageAddr);
              VTable.Assert(currAddr <= pageAddr);
              UIntPtr nextPageStart = PageTable.PagePad(currAddr+1);
              while (currAddr < pageAddr) {
                  if (Allocator.IsAlignment(currAddr)) {
                      currAddr += UIntPtr.Size;
                  } else if (BumpAllocator.IsUnusedSpace(currAddr)) {
                      currAddr = PageTable.PagePad(currAddr) + PreHeader.Size;
                  } else {
                      if (currAddr >= nextPageStart) {
                          InteriorPtrTable.SetFirst(currAddr);
                          nextPageStart = PageTable.PagePad(currAddr+1);
                      }
                      currAddr += ObjectSize(currAddr);
                  }
              }
          }
          currAddr = Allocator.SkipAlignment(currAddr);
          return currAddr;
      }

      /*
       * Returns a pointer past the last object _that_fits_completely_ on
       * the given page.  Note that the "last" object on a page may
       * actually start on a previous page.
       */
      internal static UIntPtr Last(UIntPtr page)
      {
          UIntPtr currAddr = InteriorPtrTable.First(page);
          UIntPtr endAddr = PageTable.PageAddr(page + 1);
          // Look out for the unused space token: this page may not
          // have been completely allocated: its "first" object might not
          // be valid.
          if (BumpAllocator.IsUnusedSpace(currAddr) || currAddr >= endAddr) {
              // Back up to the previous object.  Should be fast
              // since First updated the InteriorPtrTable entries.
              currAddr = Before(PageTable.PageAddr(page));
          }
          // REVIEW this is very similar to Find(addr) below.
          VTable.Assert(currAddr <= endAddr);
          while (true) {
              // Watch out for alignment padding; advance the pointer if
              // it points to a syncblock index rather than a vtable
              // pointer.  Note that we must do this before scrolling,
              // since the page table value was set before we knew the
              // required alignment.
              if (Allocator.IsAlignment(currAddr)) {
                  currAddr += UIntPtr.Size;
              } else if (BumpAllocator.IsUnusedSpace(currAddr)) {
                  UIntPtr nextAddr =
                      PageTable.PagePad(currAddr) + PreHeader.Size;
                  if (nextAddr >= endAddr) {
                      return currAddr;
                  } else {
                      currAddr = nextAddr;
                  }
              } else {
                  VTable.Assert(currAddr <= endAddr);
                  UIntPtr size = ObjectSize(currAddr);
                  UIntPtr postAddr = currAddr + size;
                  if (postAddr > endAddr) {
                      if (postAddr - PreHeader.Size > endAddr) {
                          // The object spills over onto the next page
                          return currAddr;
                      } else {
                          // The object ended at or before the page boundary
                          return postAddr;
                      }
                  } else {
                      currAddr = postAddr;
                  }
              }
          }
      }

      // Finds the object base for an interior pointer.  In the case of a
      // pointer to the tail of an object and the head of another, it will
      // return the former object (the one whose tail we point at).  To
      // get the base pointer for a pointer into the pre-header, you should
      // add PreHeader.Size before calling this.
      internal static UIntPtr Find(UIntPtr addr) 
      {
          UIntPtr page = PageTable.Page(addr);
          UIntPtr currAddr = InteriorPtrTable.First(page);
          // Look out for the unused space token: this page may not
          // have been completely allocated: its "first" object might not
          // be valid.
          if (BumpAllocator.IsUnusedSpace(currAddr) || currAddr > addr) {
              // Back up to the previous object.  Should be fast
              // since First updated the InteriorPtrTable entries.
              currAddr = Before(PageTable.PageAddr(page));
          }
          VTable.Assert(!BumpAllocator.IsUnusedSpace(currAddr),
                        "InteriorPtrTable.Find 0");
          VTable.Assert(currAddr <= addr, "InteriorPtrTable.Find 1");
          while (true) {
              // Watch out for alignment padding; advance the pointer if
              // it points to a syncblock index rather than a vtable
              // pointer.  Note that we must do this before scrolling,
              // since the page table value was set before we knew the
              // required alignment.
              if (Allocator.IsAlignment(currAddr)) {
                  currAddr += UIntPtr.Size;
              } else if (BumpAllocator.IsUnusedSpace(currAddr)) {
                  UIntPtr postAddr =
                      PageTable.PagePad(currAddr) + PreHeader.Size;
                  VTable.Assert(postAddr <= addr, "InteriorPtrTable.Find 2");
                  currAddr = postAddr;
              } else {
                  VTable.Assert(currAddr <= addr, "InteriorPtrTable.Find 3");
                  UIntPtr size = ObjectSize(currAddr);
                  VTable.Assert(size >= UIntPtr.Zero,
                                "InteriorPtrTable.Find 4");
                  UIntPtr postAddr = currAddr + size;
                  if (postAddr > addr) {
                      return currAddr;
                  } else {
                      currAddr = postAddr;
                  }
              }
          }
      }

      internal static unsafe UIntPtr ObjectSize(UIntPtr addr) {
          UIntPtr vtableAddr = Allocator.GetObjectVTable(addr);
          UIntPtr vtablePage = PageTable.Page(vtableAddr);
          if (PageTable.IsGcPage(vtablePage)) {
              // The vtable field is really a forwarding pointer
              vtableAddr = Allocator.GetObjectVTable(vtableAddr);
          } else {
              // Clear the lowest bits, if set
              vtableAddr &= ~((UIntPtr)3);
          }
          VTable vtable =
              Magic.toVTable(Magic.fromAddress(vtableAddr));
          return ObjectLayout.ObjectSize(addr, vtable);
      }

      [Inline]
      internal static unsafe void SetFirst(UIntPtr newAddr) {
          VTable.Assert(PageTable.IsGcPage(PageTable.Page(newAddr)),
                        "SetFirst on a non-GC page");
          UIntPtr page = PageTable.Page(newAddr);
          UIntPtr offset = newAddr - PageTable.PageAddr(page);
          PageTable.SetExtra(page, unchecked((uint)(offset+OFFSET_SKEW)));
      }

      [Inline]
      internal static unsafe void ClearFirst(UIntPtr page) {
          PageTable.SetExtra(page, OFFSET_NO_DATA);
      }

      [Inline]
      internal static unsafe void ClearFirst(UIntPtr startPage, 
                                             UIntPtr endPage)
      {
          PageTable.SetExtra(startPage, endPage - startPage, OFFSET_NO_DATA);
      }

      [System.Diagnostics.Conditional("DEBUG")]
      internal static unsafe void VerifyFirst(UIntPtr previousObjectAddr,
                                              UIntPtr objectAddr)
      {
          UIntPtr page = PageTable.Page(objectAddr);
          if (previousObjectAddr != UIntPtr.Zero) {
              UIntPtr previousPage = PageTable.Page(previousObjectAddr);
              UIntPtr pageCursor = previousPage + 1;
              while (pageCursor < page) {
                  uint cursorOffset = PageTable.Extra(pageCursor);
                  UIntPtr objAddr = (PageTable.PageAddr(pageCursor) +
                                     cursorOffset - OFFSET_SKEW);
                  if(!(cursorOffset <= OFFSET_NO_DATA ||
                       BumpAllocator.IsUnusedSpace(objAddr) ||
                       Allocator.IsAlignment(objAddr) ||
                       BumpAllocator.IsRestOfPageZero(objAddr))) {
                      VTable.DebugPrint
                          ("cursorOffset={0:x} OFFSET_NO_DATA={1:x} objAddr={2:x} unused={3} isalign={4} iszero={5}\n",
                           __arglist((cursorOffset),
                                     (OFFSET_NO_DATA),
                                     ((long)objAddr),
                                     (BumpAllocator.IsUnusedSpace(objAddr)),
                                     (Allocator.IsAlignment(objAddr)),
                                     (BumpAllocator.IsRestOfPageZero(objAddr))));
                  }
                  VTable.Assert(cursorOffset <= OFFSET_NO_DATA ||
                                BumpAllocator.IsUnusedSpace(objAddr) ||
                                Allocator.IsAlignment(objAddr) ||
                                BumpAllocator.IsRestOfPageZero(objAddr),
                                "VerifyFirst 1");
                  pageCursor++;
              }
          }
          uint offset = PageTable.Extra(page);
          if (offset > OFFSET_NO_DATA) {
              UIntPtr firstAddr =
                  PageTable.PageAddr(page) + offset - OFFSET_SKEW;
              if(!(firstAddr == objectAddr ||
                   (firstAddr + UIntPtr.Size == objectAddr &&
                    Allocator.IsAlignment(firstAddr)))) {
                  VTable.DebugPrint
                      ("firstAddr={0:x} objectAddr={1:x} isalign={2}\n",
                       __arglist(((long)firstAddr),
                                 ((long)objectAddr),
                                 (Allocator.IsAlignment(firstAddr))));
              }
              VTable.Assert(firstAddr == objectAddr ||
                            (firstAddr + 4 == objectAddr &&
                             Allocator.IsAlignment(firstAddr)),
                            "VerifyFirst 2");
          }
      }

  }

}

//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

//#define DEBUG_OFFSETTABLE

namespace System.GCs {

  using Microsoft.Bartok.Runtime;
  using System.Threading;
  using System.Runtime.CompilerServices;

  internal unsafe class OffsetTable {
   
      // OffsetTable is to identify objects in cards. Each card has one
      // entry in the offsetTable.
      // An entry in the offsetTable for a card has a special value 
      // (NoObjPtrToCard) if no object pointer points to the card.
      // Otherwise, it is an offset of the last object in the card
      // relative to the beginning of the card. 
      // Note: an object pointer points to the byte below its header,
      // not the header itself. That is vtable for non reference counting
      // collector, and refCount for reference counting.

      private static byte *offsetTableBase;

      // Special offset indicating that in a card, there is no object
      // pointer to it. We make it as -1, and the effective
      // offset of an pointer is within 0~127 when an offsetTable entry
      // is 1 byte, or 0~2**15-1 if it is 2 bytes. However, to avoid time
      // to initialize the offsetTable with -1, we simply add an bias 1
      // to all the them, such that the special offset is 0, and the effective
      // ones are within 1~128 (or 1~2**15). Correspondingly, in fetching
      // the offset from the able, we should deduct the bias to get the real
      // offset.
      
      private static UIntPtr NoObjPtrToCard {
         get { return (UIntPtr)0x0;}
      }     

      // The  bias.
      
      private static byte OffsetBias {
         get { return 0x1;}
      }           

      // Assume pointers are naturally aligned within a card. Then
      // its least 2 or 3 significant bits are 0 and need not be recorded.

      private static byte OffsetIgnorableBits {
         get {
            VTable.Assert(UIntPtr.Size == 4 || UIntPtr.Size == 8, 
                     "Not supported pointer type");                     
            if (UIntPtr.Size == 4) {
               return 2;
            } else {
               return 3;
            }
         }
      }

      // An entry in the offsetTable needs to be either 1 byte or 2 bytes,
      // depending on the size of a card.
      // Given one byte for an entry, we can represent 128 effective offsets,
      // and one special offset NoObjPtrToCard. For x64,
      // UIntPtr.Size*128 = 2**10. For x86, UIntPtr.Size * 128 = 2**9.
      // That is, the size of a card is no bigger than 2**10 or 2**9.
      // Given two bytes for an entry, we can represent 2**15 effective
      // offsets, and one special offset. The size of card is no bigger than
      // 2**18 or 2**17.
 
      private static byte EntryBytes {
         get {
            VTable.Assert(UIntPtr.Size == 4 || UIntPtr.Size == 8, 
                     "Not supported pointer type");         
            if ((UIntPtr.Size == 4 && CardTable.CardBits <= 9) ||
                 (UIntPtr.Size == 8 && CardTable.CardBits <= 10)) {
               return 1;
            } else {
               VTable.Assert((UIntPtr.Size == 4 && CardTable.CardBits <= 17) ||
                                     (UIntPtr.Size == 8 && CardTable.CardBits <= 18),
                                     "Card size is unreasonable large");
               return 2;
            }
         }
      }
      
      internal static void Initialize(UIntPtr totalCards) {
         UIntPtr offsetTablePtr = PageManager.AllocateNonheapMemory(null,  
            ((UIntPtr)EntryBytes)*totalCards);
         VTable.Assert(offsetTablePtr != UIntPtr.Zero, "OffsetTable.Initialize: no memory");
         
         offsetTableBase = (byte*)(offsetTablePtr - CardTable.FirstCardNo);

         // The memory of offset table should have already been cleaned
         
         for (UIntPtr c=CardTable.FirstCardNo; c<CardTable.FirstCardNo+totalCards;c++) {
            VTable.Assert(NoObjectPtrToTheCard(c), "offset table initialization error");
         }
      }
      
      [Inline]
      private static void SetNoObjPtrToCard(UIntPtr c)
      {
         VTable.Assert(CardTable.IsValidCardNo(c), "SetNoObjPtrToCard: invalid card no");
         SetCompressedBiasedOffset(c, NoObjPtrToCard);
      }

      [Inline]
      internal static bool NoObjectPtrToTheCard(UIntPtr c)
      {
         VTable.Assert(CardTable.IsValidCardNo(c), "NoObjectPtrToTheCard: invalid card no");
         return (GetCompressedBiasedOffset(c)  == NoObjPtrToCard);
      }

      [Inline]
      internal static void SetOffset(UIntPtr c, UIntPtr offset)
      {            
         VTable.Assert((offset >> OffsetIgnorableBits) << OffsetIgnorableBits
                                 == offset, "offset should be multiple of pointer size");
         VTable.Assert(NoObjectPtrToTheCard(c) || GetOffset(c) < offset,
               "A smaller offset offset is set to card ");

         SetCompressedBiasedOffset(c, (offset >> OffsetIgnorableBits) + (UIntPtr)OffsetBias);
      }

      [Inline]
      internal static UIntPtr GetOffset(UIntPtr c)
      {
         UIntPtr offset = GetCompressedBiasedOffset(c) - (UIntPtr)OffsetBias;
         return offset << OffsetIgnorableBits;
      }            

      [Inline]
      private static bool IsValidCompressedBiasedOffset(UIntPtr value) 
      {
         return value <= ((UIntPtr)2<<(EntryBytes * 8 -1));
      }

      [Inline]
      private static void SetCompressedBiasedOffset(UIntPtr c, UIntPtr value)
      {
         VTable.Assert(IsValidCompressedBiasedOffset(value), "Invalid compressed biased value");
         if (EntryBytes == 1) {
            *(offsetTableBase + c)  = (byte)value;
         } else {
            *((short*)offsetTableBase + c)  = (short)value;        
         }
      }

      [Inline]
      private static UIntPtr GetCompressedBiasedOffset(UIntPtr c)
      {
         if (EntryBytes == 1) {
            return (UIntPtr) (*(offsetTableBase + c));
         } else {
            return (UIntPtr)(*((short*)offsetTableBase + c));       
         }
      }

      // OffsetTable records all objects promoted or directly allocated in mature
      // generation. 
      
      internal static void SetLast(UIntPtr objPtr)
      {      
         VTable.Assert(PageTable.IsGcPage(PageTable.Page(objPtr)), "Not GC page");
 
         UIntPtr card = CardTable.CardNo(objPtr);                           
         UIntPtr mask = (UIntPtr)(CardTable.CardSize -1);
         UIntPtr offset = objPtr & mask;
         VTable.Assert(offset < CardTable.CardSize, "Overflow");
         SetOffset(card, offset);    
#if DEBUG_OFFSETTABLE         
         VTable.DebugPrint("SetLast objPtr {0:x8}, card {1:x8}, offset {2:x8}\n",
                  __arglist(objPtr, card, offset));
#endif                  
      }

      internal static UIntPtr FirstObjPtrWithFieldInCard(UIntPtr c)
      {
         VTable.Assert(CardTable.IsValidCardNo(c), "Not valid card no");
         VTable.Assert(CardTable.IsMyLiveGcCard(c), "Not my live GC card");

         UIntPtr cardAddr = CardTable.CardAddr(c);
         UIntPtr nextCardAddr = CardTable.NextCardAddr(c);

         // Scan backward. May go to zombie areas
         
         UIntPtr cardBefore = c -1;
         while (cardBefore >= CardTable.FirstCardNo &&
            OffsetTable.NoObjectPtrToTheCard(cardBefore) &&
            CardTable.IsMyGcCard(cardBefore)){
               cardBefore --;
         }
         
         UIntPtr ptr;
         
         if (cardBefore < CardTable.FirstCardNo || 
              !CardTable.IsMyGcCard(cardBefore)) {
            
            // this case happens when c is the first live card that has an object.

            VTable.Assert(CardTable.IsMyGcCard(cardBefore+1),
                  "The next card must be a GC card");
            VTable.Assert(CardTable.CardAddr(cardBefore+1) == 
                  CardTable.PageAddrOfCard(cardBefore+1),
                  "The next card must be at the boundary of a page");
                           
            UIntPtr pageAddr = CardTable.PageAddrOfCard(cardBefore+1);
            ptr =PtrToNextObject(pageAddr, (UIntPtr)PreHeader.Size, nextCardAddr);
         } else {         
            VTable.Assert(!OffsetTable.NoObjectPtrToTheCard(cardBefore),
                  "A card with an object must have been found");
            ptr = CardTable.CardAddr(cardBefore) +
                     OffsetTable.GetOffset(cardBefore);
         }
         VTable.Assert(ptr < nextCardAddr, "No objptr in this card");

         // Scan forward. Update offset table in the course.

         UIntPtr currentPtr = ptr;
         while (currentPtr < cardAddr) { 
               UIntPtr size = OffsetTable.ObjectSize(currentPtr);
               if (currentPtr + size - PreHeader.Size > cardAddr) {     
                  VTable.Assert(CardTable.CardGeneration(CardTable.CardNo(currentPtr)) == 
                        CardTable.CardGeneration(c), 
                        "The whole object must be in the same generation");
                  break;
               } else {               
                  ptr = currentPtr;
                  currentPtr = PtrToNextObject(currentPtr, size, nextCardAddr);
                  VTable.Assert(CardTable.CardNo(ptr) <= CardTable.CardNo(currentPtr), 
                        "Previous ptr should be before current ptr");
                  if (CardTable.CardNo(ptr) < CardTable.CardNo(currentPtr)) {
                        UIntPtr ptrC = CardTable.CardNo(ptr);
                        UIntPtr offsetC = ptr - CardTable.CardAddr(ptrC);                        
                        if (offsetC > GetOffset(ptrC)) {                           
                              SetOffset(ptrC, offsetC);                              
                        }
                  }
              }
         }            
         VTable.Assert(currentPtr != UIntPtr.Zero, "current ptr is zero");
         VTable.Assert(currentPtr < nextCardAddr, "No objptr found in this card");  
        
#if DEBUG_OFFSETTABLE
         UIntPtr temp = OffsetTable.FirstPtrFromInteriorTable(c);
         if (temp != currentPtr) {
            VTable.DebugPrint("Found ptr ({0:x8}) inconsistent with first ptr from interior table({1:x8})\n",
                  __arglist(currentPtr, temp));            
            VTable.Assert(false);
         }                    
#endif

         return currentPtr;       
      }

      // The next object after the current object and below the limit
      
      [Inline]
      internal static UIntPtr PtrToNextObject(UIntPtr objPtr, UIntPtr size, UIntPtr limit)
      {
         return BumpAllocator.SkipNonObjectData(objPtr + size, limit);
      }            

      [Inline]
      internal static void ClearCards(UIntPtr c1, UIntPtr c2)
      {
         for (UIntPtr i = c1; i <= c2; i++) {
            SetNoObjPtrToCard(i);
         }   
#if DEBUG_OFFSETTABLE
         VTable.DebugPrint("ClearLast from {0:x8} to {1:x8}\n", __arglist(c1, c2));
#endif
      }
      
      internal static void ClearLast(UIntPtr from, UIntPtr to)
      {
         UIntPtr first = CardTable.CardNo(from);
         UIntPtr last = CardTable.CardNo(to);
         ClearCards(first, last);
      }

      // Copied from InteriorPtrTable.cs

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
         
#if DEBUG_OFFSETTABLE
      private static UIntPtr FirstPtrFromInteriorTable(UIntPtr c)
      {   
          UIntPtr cardAddr = CardTable.CardAddr(c);
          UIntPtr nextCardAddr = CardTable.NextCardAddr(c);
          UIntPtr page = PageTable.Page(cardAddr);
          UIntPtr pageAddr = PageTable.PageAddr(page);
          UIntPtr currAddr;

          if (page == 0) {
               currAddr =PtrToNextObject(pageAddr, 
                              (UIntPtr)PreHeader.Size, nextCardAddr);
          } else {
               short offset = PageTable.Extra(page);
               currAddr = UIntPtr.Zero;
               if (offset != InteriorPtrTable.OFFSET_NO_DATA) {
                  currAddr = pageAddr + (offset - InteriorPtrTable.OFFSET_SKEW);
               }

               // In general, we expect currAddr <= cardAddr. Or in the extreme
               // case, when the object starts from the page boundary,
               // currAddr - Object.HEADER_BYTES <= cardAddr. The contrary
               // cases has to be handled by searching previous pages.
               
               if (currAddr == UIntPtr.Zero ||
                    (currAddr > cardAddr &&    
                      currAddr - PreHeader.Size > cardAddr)) {
               
                  // look from previous pages, in case that an object on
                  // them spans to the current page. In that case, we should 
                  // should use that object's ptr.

                  currAddr = InteriorPtrTable.Last(page -1);

                  // Usually, Last() returns a pointer before or at the page
                  // boundary. However, there is one exception: when an object
                  // exactly fits to the last byte of the previous page, and the next
                  // object starts right from the page boundary (the first byte of
                  // the next page), then the pointer to this next object is returned.
                  // Example found: objPtr =3d09fa8, size=60, pageboundary=
                  // 3d0a000, next objPtr=3d0a008. Then returned pointer is
                  // 3d0a008, which is beyond the page boundary.
               
                  VTable.Assert(currAddr <= pageAddr || 
                     currAddr - PreHeader.Size <= pageAddr,
                     "object is expected before page or right at the beginning of it");
              }
          }
          VTable.Assert(currAddr < nextCardAddr, "object is expected before next card");
          
          while (currAddr < nextCardAddr) {
              if (Allocator.IsAlignment(currAddr)) {
                  currAddr += UIntPtr.Size;
              } else if (BumpAllocator.IsUnusedSpace(currAddr)) {
                  currAddr = PageTable.PagePad(currAddr) + PreHeader.Size;
              } else {
                  UIntPtr size = InteriorPtrTable.ObjectSize(currAddr);                  
                  if (currAddr + size - PreHeader.Size > cardAddr) {                     
                     return currAddr;
                  }
                  currAddr += size;                   
             }
        }       
        VTable.Assert(false, "No obj ptr found by looking at interior table");
        return UIntPtr.Zero;
     }
#endif
   }
}

//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


//#define DEBUG_CARDS

namespace System.GCs {

  using Microsoft.Bartok.Runtime;
  using System.Threading;
  using System.Runtime.CompilerServices;

  internal unsafe class CardTable : RememberedSet {

      internal static CardTable instance;

      private static UIntPtr firstCardNo; 
      private static UIntPtr totalCards; 

      // To save time in computing the correct card to be marked,
      // set the value of cardTableBase such that given a card number c, 
      // the corresponding card entry is simply cardTableBase+c. 
      // Note: the card number c of address p is p >>CardBits. Since our
      // heap does not necessarily start from address 0, the card numbers
      // may NOT start  from 0, either.
      
      private static byte *cardTablePtr; // real start of the card table     
      private static byte *cardTableBase; 

      // A card is clean before any pointer update in it. It is dirty after an
      // update. During a collection, if the card has inter-generational
      // pointers, the pointers are traced. 
      
      internal enum CardType: byte{
         Clean = 0,
         Dirty = 1
      }

      // CardBits, CardSize, etc.  are defined as properties instead of
      // const int to avoid calling static constructor of CardTye
      // during GC.cctor.
      
      // TODO: fine tune the CardBits for performance
      
      internal static byte CardBits {
         get { 
            if (UIntPtr.Size == 4) {
               return 9;
            } else if (UIntPtr.Size == 8) {
               return 10;
            } else {
               VTable.Assert(false, "Not supported pointer type");
               return 0xff;
            }
         }
      }
      
      internal static UIntPtr CardSize {
         get { return (UIntPtr)1 << CardBits;}  // size of a card in bytes
      }
      
      internal static UIntPtr FirstCardNo {
         get {
            return firstCardNo;
         }
      }

      internal static void Initialize() {
         // The card table covers all the heap. Below is not accurate heap
         // size. It includes all the memory space, starting from address 0.
         // TODO: find more accurate heap size and start
         
         UIntPtr heapSize = PageTable.pageTableCount * PageTable.PageSize;
         VTable.Assert((heapSize >> CardBits) << CardBits == heapSize,
               "Assumption: pageSize is expected to be multiple of CardSize");
         UIntPtr heapStart = (UIntPtr)0;
         
         totalCards = heapSize >> CardBits;
         firstCardNo = heapStart >> CardBits;

         UIntPtr tablePtr =PageManager.AllocateNonheapMemory(null,  totalCards);
         VTable.Assert(tablePtr != UIntPtr.Zero);         
         cardTablePtr = (byte*) tablePtr;
         cardTableBase = (byte*)(tablePtr - firstCardNo);
         
         CardTable.instance = (CardTable)
              BootstrapMemory.Allocate(typeof(CardTable));

         OffsetTable.Initialize(totalCards);

         for (UIntPtr c = firstCardNo; c < firstCardNo + totalCards; c++) {
            VTable.Assert(!CardIsDirty(c), "Card table initialization error");
         }
      }

      [Inline]
      internal static bool IsValidCardNo(UIntPtr c)
      {
         return (c >= firstCardNo && c < firstCardNo + totalCards);
      }

      [Inline]
      internal static UIntPtr CardNo(UIntPtr addr)
      {
         UIntPtr c = addr >> CardBits;
         VTable.Assert(IsValidCardNo(c), "CardNo invalid");
         return c;
      }
      
      [Inline]
      internal static UIntPtr CardAddr(UIntPtr c)
      {
         VTable.Assert(IsValidCardNo(c), "CardAddr invalid");
         return c << CardBits;
      }

      [Inline]
      internal static UIntPtr NextCardAddr(UIntPtr c)
      {
         VTable.Assert(IsValidCardNo(c), "NextCardAddr invalid");
         return CardAddr(c) + CardSize;
      }
      
      // The following two Clean functions are supposed to reset unused
      // entries in the remembered set. They are not meaningful for cardtable.

      [Inline]
      internal override void Clean() {
         // Nothing to do
      }

      [Inline]      
      internal override void Clean(Thread thread) {
         // Nothing to do        
      }

      // There is no duplicate entries in cardtable.
      
      internal override void Uniquify() {
         // Nothing to do
      }

      internal override void Reset() {
         Util.MemClear((UIntPtr)cardTablePtr, totalCards);
      }

      [Inline]
      private static bool CardIsDirty(UIntPtr c)
      {
         VTable.Assert(IsValidCardNo(c), "CardIsDirty invalid");
         return (*(cardTableBase+c) == (byte)CardType.Dirty);
      }

      [Inline]
      internal static PageType CardGeneration(UIntPtr c)
      {
         VTable.Assert(IsValidCardNo(c), "CardGeneration invalid");
         return PageTable.Type(PageTable.Page(CardAddr(c)));
      }

      [Inline]
      internal static bool IsMyLiveGcCard(UIntPtr c)
      {
         VTable.Assert(IsValidCardNo(c), "IsMyLiveGcCard invalid");
         UIntPtr page = PageTable.Page(CardAddr(c));
         return (PageTable.IsMyPage(page) && 
                        PageTable.IsLiveGcPage(PageTable.Type(page)));
      }

      [Inline]
      internal static bool IsMyGcCard(UIntPtr c)
      {
         VTable.Assert(IsValidCardNo(c), "IsMyGcCard invalid");
         UIntPtr page = PageTable.Page(CardAddr(c));
         return (PageTable.IsMyGcPage(page));
      }

      [Inline]
      internal static UIntPtr PageAddrOfCard(UIntPtr c)
      {
         return  PageTable.PageAlign(CardAddr(c));
      }                         

      [Inline]
      internal override void RecordReference(ref Object reference,
                                             Object toObj)
      {
          Record((UIntPtr) Magic.toPointer(ref reference));
      }

      [Inline]
      internal override void RecordReference(UIntPtr* fromAddr,
                                             Object toObj)
      {
          Record((UIntPtr) fromAddr);
      }

      // So far, we scan the whole object that has any dirty field. So we just 
      // make the first card of this cloned object dirty.
      // TODO: make all the cards of the object dirty if we scan fields
      // in the dirty card only.
      
      [Inline]
      internal override void RecordClonedObject(Object clonedObject)
      {
          Record(Magic.addressOf(clonedObject));
      }

      [RequiredByBartok]
      [Inline]
      public static void Record(UIntPtr fromAddr)    
      {
         *(cardTableBase + CardNo(fromAddr)) = (byte)CardType.Dirty;
      }         
            
      internal override void Scan(NonNullReferenceVisitor ptrVisitor, 
         PageType genToCollect)
      {   
#if DEBUG_CARDS 
         VTable.DebugPrint("************  Scan to collect generation {0:x8} ******\n", 
               __arglist(genToCollect));                  
         for (UIntPtr i = firstCardNo; i < firstCardNo + totalCards; i++) {
            if (CardIsDirty(i)) {
               VTable.DebugPrint("dirty card {0:x8} gen {1:x8}\n", __arglist(i, CardGeneration(i)));
            }               
         }
#endif                  
      
         for (UIntPtr c = firstCardNo; c < firstCardNo + totalCards; ) {
            if (CardIsDirty(c) && IsMyLiveGcCard(c) && 
               CardGeneration(c) > genToCollect) {
                  UIntPtr last = c + 1;
                  while (last < firstCardNo + totalCards && CardIsDirty(last) && 
                     IsMyLiveGcCard(last) && 
                     CardGeneration(last) > genToCollect) {
                        last++;
                  }
#if DEBUG_CARDS 
                  VTable.DebugPrint("Scan from {0:x8} to {1:x8} to collect gen {2:x8}\n",
                        __arglist(c, last-1, genToCollect));                  
#endif                  
                  VisitObjectsInCards(ptrVisitor, c, last - 1);
                  c = last;
               } else {
                  c++;
               }
         }
#if DEBUG_CARDS 
         VTable.DebugPrint("************ End Scan ******\n");                  
#endif                           
      }

      private static void VisitObjectsInCards(NonNullReferenceVisitor ptrVisitor,
         UIntPtr first, UIntPtr last)
      {
         UIntPtr objectPtr = OffsetTable.FirstObjPtrWithFieldInCard(first);
         VTable.Assert(objectPtr != UIntPtr.Zero, "No first obj ptr");

         // TODO: in semispace.Visit, update cards in visiting promoted objects.
         // So far, since we have only two generations, and after scanning, all nursery
         // objects are promoted to mature generation,  thus there is no inter-generational
         // pointers anymore, and we do not need to update cards during visit. But we
         // need to do that once we have more than two generations.

         UIntPtr limit = NextCardAddr(last);
         
         while (objectPtr != UIntPtr.Zero && objectPtr < limit) {
#if DEBUG_CARDS
            VTable.DebugPrint("     visiting obj ptr {0:x8}\n", __arglist(objectPtr));      
#endif                              
            Object obj = Magic.fromAddress(objectPtr);
            UIntPtr objSize = ptrVisitor.VisitReferenceFields(obj);
            UIntPtr nextObjectPtr = OffsetTable.PtrToNextObject(objectPtr, objSize, limit);  
            VTable.Assert(CardNo(objectPtr) <= CardNo(nextObjectPtr),
                  "Next object should be below the current one");
            if (CardNo(objectPtr) < CardNo(nextObjectPtr)) {
               UIntPtr c = CardNo(objectPtr);
               UIntPtr offset = objectPtr - CardAddr(c);
               if ( offset > OffsetTable.GetOffset(c)) {
                  OffsetTable.SetOffset(c, offset);
               }
            }
            objectPtr = nextObjectPtr;
         }
      }
   }
}

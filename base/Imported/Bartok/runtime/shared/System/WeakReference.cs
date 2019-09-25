//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


namespace System {

  using Microsoft.Bartok.Runtime;
  using System.Threading;
  using System.Runtime.CompilerServices;
  using System.GCs;

  /// <summary>
  /// This class implements weak references.
  /// 
  /// When a new weak references is allocated it is atomically linked 
  /// onto a singly linked list of weak references.
  /// 
  /// During a garbage collection this chain is traversed and references 
  /// are updated or cleared.
  /// 
  /// There are two modes of processing weak references.
  /// 
  ///     1. Ignoring 'Long' References that track resurrection and
  ///        only updating references that should be cleared when the
  ///        object is finalized.
  ///     2. Updating all reference types.
  ///    
  /// In any collection at least the second method must be called to 
  /// ensure no dangling pointers are created.
  /// 
  /// BUGBUG: At the moment it is possible to have a weak reference that
  /// is unlinked from the chain and then resurrected as reachable from 
  /// a finalizable object!
  /// </summary>
  [CCtorIsRunDuringStartup]
#if !SINGULARITY
  [Serializable]
#endif
  public unsafe class WeakReference {

      /// <summary>
      /// The dummy head reference to simplify traversal logic.
      /// </summary>
      private static readonly WeakReference headRef;

      /// <summary>
      /// The weak reference to the object
      /// </summary>
      private UIntPtr objPtr;

      /// <summary>
      /// The next reference on the chain.
      /// </summary>
      private UIntPtr nextRef;

      /// <summary>
      /// Does this reference stay alive during finalization of the target?
      /// </summary>
      private bool trackResurrection;
      
      private WeakReference() {}

      /// <summary>
      /// Construct a 'Short' weak reference.
      /// </summary>
      public WeakReference(Object target) : this(target, false) {}

      /// <summary>
      /// Construct a weak reference and link it onto the chain, 
      /// specifying if it is to track an object through finalization.
      /// </summary>
      public WeakReference(Object target, bool trackResurrection) {
          this.Target = target;
          this.trackResurrection = trackResurrection;

          UIntPtr thisPtr = Magic.addressOf(this);
          do {
              this.nextRef = headRef.nextRef;
          } while (this.nextRef != Interlocked.CompareExchange(
              ref headRef.nextRef,
              thisPtr,
              this.nextRef));
      }

      /// <summary>
      /// Is the object alive?
      /// </summary>
      public virtual bool IsAlive {
          get {
              return this.objPtr != UIntPtr.Zero;
          }
      }

      /// <summary>
      /// Get or set target of the object. Null if the object has been
      /// collected.
      /// </summary>
      public virtual Object Target {
          get {
              return Barrier.WeakRefRead(this.objPtr, 0);
          }
          set {
              this.objPtr = Barrier.WeakRefWrite(value, 0);
          }
      }

      /// <summary>
      /// Should this reference track objects through finalization?
      /// </summary>
      public virtual bool TrackResurrection {
          get {
              return trackResurrection;
          }
      }

      /// <summary>
      /// This method performs the processing of weak references for GC.
      /// 
      /// It essentially walks a list unlinking weak reference objects 
      /// that are not live and updating references as necessary.
      /// </summary>
      internal static
      void Process(DirectReferenceVisitor updateReferenceVisitor,
                   bool copyFirst, bool ignoreLong)
      {

          // Head ref is a dummy ref object.
          WeakReference wr = headRef;
          
          while (wr.nextRef != UIntPtr.Zero) {
              if (ignoreLong) {
                  WeakReference tmp =
                      Magic.toWeakReference(Magic.fromAddress(wr.nextRef));

                  if (tmp.trackResurrection) {
                      wr = tmp;
                      continue;
                  }
                  
              }

              UIntPtr nextPtr = wr.nextRef;

              fixed (UIntPtr * loc = &wr.nextRef) {
                  // update the reference 
                  updateReferenceVisitor.Visit(loc);
              }

              WeakReference next;

              if (wr.nextRef == UIntPtr.Zero) {
                  // remove next from the chain and continue
                  next =
                      Magic.toWeakReference(Magic.fromAddress(nextPtr));
                  wr.nextRef = next.nextRef;
                  continue;
              }

              // Updating old or new location?
              if (copyFirst) {
                  next =
                      Magic.toWeakReference(Magic.fromAddress(wr.nextRef));
              } else {
                  next =
                      Magic.toWeakReference(Magic.fromAddress(nextPtr));
              }

              fixed (UIntPtr * loc = &next.objPtr) {
                  if (*loc != UIntPtr.Zero) {
                      // Update Reference
                      updateReferenceVisitor.Visit(loc);
                  }
              }

              // Continue
              wr = next;
          }
      }

      /// <summary>
      /// Class constructor, set up dummy head.
      /// </summary>
      static WeakReference() {
          headRef = new WeakReference();
      }
  }
}

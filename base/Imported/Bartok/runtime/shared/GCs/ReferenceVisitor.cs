//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs
{
    using Microsoft.Bartok.Runtime;
    using System.Runtime.CompilerServices;

    internal abstract class ReferenceVisitor {

        internal struct ObjectDescriptor {
            [ManualRefCounts]
            [Inline]
            internal ObjectDescriptor(VTable vtable, UIntPtr objectBase) :
                this(vtable, objectBase, UIntPtr.Zero, UIntPtr.Zero,
                     null, null)
            {
            }

            [ManualRefCounts]
            [Inline]
            internal ObjectDescriptor(VTable vtable, UIntPtr objectBase,
                                      UIntPtr secondBase) :
                this(vtable, objectBase, secondBase, UIntPtr.Zero, null, null)
            {
            }

            [ManualRefCounts]
            [Inline]
            internal ObjectDescriptor(VTable vtable,
                                      UIntPtr objectBase,
                                      UIntPtr secondBase,
                                      UIntPtr extra) :
                this(vtable, objectBase, secondBase, extra, null, null)
            {}

            [ManualRefCounts]
            [Inline]
            internal ObjectDescriptor(VTable vtable,
                                      UIntPtr objectBase,
                                      UIntPtr secondBase,
                                      UIntPtr extra,
                                      Object realObjectBase,
                                      Object realSecondBase)
            {
                this.vtable = vtable;
                this.objectBase = objectBase;
                this.secondBase = secondBase;
                this.extra = extra;
                this.realObjectBase = realObjectBase;
                this.realSecondBase = realSecondBase;
            }

            // this struct is never in the heap, so the fields should
            // be accessed the quick way.  (and no, this struct isn't
            // always accessed through a local var - it might be accessed
            // via a managed pointer in the NoInline reference fields 
            // visitor methods.)
            
            [NoBarriers]
            internal new VTable vtable;
            [NoBarriers]
            internal UIntPtr objectBase;
            [NoBarriers]
            internal UIntPtr secondBase;
            [NoBarriers]
            internal UIntPtr extra;
            [NoBarriers]
            internal Object realObjectBase;
            [NoBarriers]
            internal Object realSecondBase;
        }

        // Rationale for cutting the fact that no stack probes are permitted in this
        // tree of calls:
        //
        // There is no rationale.  It is a bug which is tracked with all the cases that
        // require fixing.
        //
        // Bug 436
        [NoStackLinkCheckTransCut]
        [ManualRefCounts]
        [Inline]
        internal virtual UIntPtr VisitReferenceFields(Object obj)
        {
            return this.VisitReferenceFields(Magic.addressOf(obj),
                                             obj.vtable);
        }

        [Inline]
        internal abstract UIntPtr VisitReferenceFields(UIntPtr objectBase,
                                                       VTable vtable);

        [Inline]
        protected abstract unsafe
        void Filter(UIntPtr *location, ref ObjectDescriptor objDesc);

        // Rationale for cutting the fact that no stack probes are permitted in this
        // tree of calls:
        //
        // There is no rationale.  This is a bug which has been filed.  It is a temporary
        // hack to break the recursion in this method.  Recursion needs to open up an
        // opportunity for stack probing.  Eventually, perhaps this method can be
        // rewritten to avoid the recursion.
        //
        // Bug 436
        [NoStackLinkCheckTransCut]
        [ManualRefCounts]
        [NoInline]
        protected unsafe
        UIntPtr VisitReferenceFieldsTemplateNoInline(ref ObjectDescriptor objDesc)
        {
            return VisitReferenceFieldsTemplate(ref objDesc);
        }

        [ManualRefCounts]
        [Inline]
        protected unsafe
        UIntPtr VisitReferenceFieldsTemplate(ref ObjectDescriptor objDesc)
        {
            UIntPtr pointerTracking = objDesc.vtable.pointerTrackingMask;
            uint objectTag = (pointerTracking & 0xf);
            UIntPtr size;
            switch (objectTag) {
              case ObjectLayout.SPARSE_TAG: {
                  UIntPtr *sparseObject = (UIntPtr *) objDesc.objectBase;
                  size = ObjectLayout.ObjectSize(objDesc.vtable);
                  pointerTracking >>= 4;
                  while (pointerTracking != 0) {
                      uint index = pointerTracking & 0xf;
                      pointerTracking >>= 4;
                      // The cast to int prevents C# from taking the
                      // index * sizeof(UIntPtr) to long:
                      UIntPtr *loc = sparseObject + (int) index;
                      this.Filter(loc, ref objDesc);
                  }
                  break;
              }
              case ObjectLayout.DENSE_TAG: {
                  // skip vtable
                  int postHeaderSize = PostHeader.Size;
                  UIntPtr *denseObject = (UIntPtr *)
                      (objDesc.objectBase + postHeaderSize);
                  size = ObjectLayout.ObjectSize(objDesc.vtable);
                  pointerTracking >>= 4;
                  while (pointerTracking != 0) {
                      if ((pointerTracking & ((UIntPtr)0x1)) != 0) {
                          this.Filter(denseObject, ref objDesc);
                      }
                      pointerTracking >>= 1;
                      denseObject++;
                  }
                  break;
              }
              case ObjectLayout.PTR_VECTOR_TAG: {
                  int postHeaderSize = PostHeader.Size;
                  uint length = *(uint*)(objDesc.objectBase + postHeaderSize);
                  size = ObjectLayout.ArraySize(objDesc.vtable, length);
                  int preHeaderSize = PreHeader.Size;
                  UIntPtr *elementAddress = (UIntPtr *)
                      (objDesc.objectBase + objDesc.vtable.baseLength -
                       preHeaderSize);
                  for (uint i = 0; i < length; i++, elementAddress++) {
                      this.Filter(elementAddress, ref objDesc);
                  }
                  break;
              }
              case ObjectLayout.OTHER_VECTOR_TAG: {
                  int postHeaderSize = PostHeader.Size;
                  uint length = *(uint*)(objDesc.objectBase + postHeaderSize);
                  size = ObjectLayout.ArraySize(objDesc.vtable, length);
                  if (objDesc.vtable.arrayOf == StructuralType.Struct) {
                      // pretend the struct is boxed and account for the
                      // presence of the vtable field
                      VTable elementVTable = objDesc.vtable.arrayElementClass;
                      UIntPtr elementMask = elementVTable.pointerTrackingMask;
                      // A structure with no references will have a SPARSE
                      // descriptor with no offset values.
                      if (elementMask != (UIntPtr) ObjectLayout.SPARSE_TAG) {
                          int preHeaderSize = PreHeader.Size;
                          UIntPtr elementAddress = (objDesc.objectBase +
                                                    objDesc.vtable.baseLength -
                                                    preHeaderSize -
                                                    postHeaderSize);
                          int elementSize = objDesc.vtable.arrayElementSize;
                          objDesc.vtable = elementVTable;
                          for (uint i = 0; i < length; i++) {
                              objDesc.objectBase = elementAddress;
                              this.VisitReferenceFieldsTemplateNoInline(ref objDesc);
                              elementAddress += elementSize;
                          }
                      }
                  }
                  break;
              }
              case ObjectLayout.PTR_ARRAY_TAG: {
                  int postHeaderSize = PostHeader.Size;
                  uint length = *(uint*)(objDesc.objectBase + postHeaderSize +
                                         sizeof(uint));
                  size = ObjectLayout.ArraySize(objDesc.vtable, length);
                  int preHeaderSize = PreHeader.Size;
                  UIntPtr *elementAddress = (UIntPtr *)
                      (objDesc.objectBase + objDesc.vtable.baseLength -
                       preHeaderSize);
                  for (uint i = 0; i < length; i++, elementAddress++) {
                      this.Filter(elementAddress, ref objDesc);
                  }
                  break;
              }
              case ObjectLayout.OTHER_ARRAY_TAG: {
                  int postHeaderSize = PostHeader.Size;
                  uint length = *(uint*)(objDesc.objectBase + postHeaderSize +
                                         sizeof(uint));
                  size = ObjectLayout.ArraySize(objDesc.vtable, length);
                  if (objDesc.vtable.arrayOf == StructuralType.Struct) {
                      // pretend the struct is boxed and account for the
                      // presence of the PostHeader
                      VTable elementVTable = objDesc.vtable.arrayElementClass;
                      UIntPtr elementMask = elementVTable.pointerTrackingMask;
                      // A structure with no references will have a SPARSE
                      // descriptor with no offset values.
                      if (elementMask != (UIntPtr) ObjectLayout.SPARSE_TAG) {
                          int preHeaderSize = PreHeader.Size;
                          int elementSize = objDesc.vtable.arrayElementSize;
                          UIntPtr elementAddress =
                              objDesc.objectBase + objDesc.vtable.baseLength -
                              preHeaderSize - postHeaderSize;
                          objDesc.vtable = elementVTable;
                          for (uint i = 0; i < length; i++) {
                              objDesc.objectBase = elementAddress;
                              this.VisitReferenceFieldsTemplateNoInline(ref objDesc);
                              elementAddress += elementSize;
                          }
                      }
                  }
                  break;
              }
              case ObjectLayout.STRING_TAG: {
                  int postHeaderSize = PostHeader.Size;
                  uint arrayLength =
                      *(uint*)(objDesc.objectBase + postHeaderSize);
                  size = ObjectLayout.StringSize(objDesc.vtable, arrayLength);
                  break;
              }
              default: {
                  // escape case
                  VTable.Assert((objectTag & 0x1) == 0,
                                "ReferenceVisitor: (objectTag & 0x1) == 0");
                  UIntPtr *largeObject = (UIntPtr *) objDesc.objectBase;
                  size = ObjectLayout.ObjectSize(objDesc.vtable);
                  int *pointerDescription = (int *) pointerTracking;
                  int count = *pointerDescription;
                  for (int i = 1; i <= count; i++) {
                      UIntPtr *loc = largeObject + *(pointerDescription+i);
                      this.Filter(loc, ref objDesc);
                  }
                  break;
              }
            }
            return size;
        }

        // Rationale for cutting the fact that no stack probes are permitted in this
        // tree of calls:
        //
        // There is no rationale.  This is a bug which has been filed.  It is a temporary
        // hack to break the recursion in this method.  Recursion needs to open up an
        // opportunity for stack probing.  Eventually, perhaps this method can be
        // rewritten to avoid the recursion.
        //
        // Bug 436
        [NoStackLinkCheckTransCut]
        [ManualRefCounts]
        protected unsafe
        void VisitReferenceFieldsTemplate(ref ObjectDescriptor objDesc,
                                          int count)
        {
            UIntPtr pointerTracking = objDesc.vtable.pointerTrackingMask;
            uint objectTag = (pointerTracking & 0xf);
            switch (objectTag) {
              case ObjectLayout.PTR_VECTOR_TAG:
              case ObjectLayout.PTR_ARRAY_TAG: {
                  UIntPtr *elementAddress = (UIntPtr *) objDesc.objectBase;
                  for (int i = 0; i < count; i++, elementAddress++) {
                      this.Filter(elementAddress, ref objDesc);
                  }
                  break;
              }
              case ObjectLayout.OTHER_VECTOR_TAG:
              case ObjectLayout.OTHER_ARRAY_TAG: {
                  if (objDesc.vtable.arrayOf == StructuralType.Struct) {
                      // pretend the struct is boxed and account for the
                      // presence of the vtable field
                      VTable elementVTable = objDesc.vtable.arrayElementClass;
                      UIntPtr elementMask = elementVTable.pointerTrackingMask;
                      // A structure with no references will have a SPARSE
                      // descriptor with no offset values.
                      if (elementMask != (UIntPtr) ObjectLayout.SPARSE_TAG) {
                          int postHeaderSize = PostHeader.Size;
                          objDesc.objectBase -= postHeaderSize;
                          objDesc.secondBase -= postHeaderSize;
                          objDesc.extra += postHeaderSize;
                          int elementSize = objDesc.vtable.arrayElementSize;
                          objDesc.vtable = elementVTable;
                          for (int i = 0; i < count; i++) {
                              this.VisitReferenceFieldsTemplateNoInline(ref objDesc);
                              objDesc.objectBase += elementSize;
                              objDesc.secondBase += elementSize;
                              objDesc.extra -= elementSize;
                          }
                          objDesc.objectBase += postHeaderSize;
                          objDesc.secondBase += postHeaderSize;
                          objDesc.extra -= postHeaderSize;
                      }
                  }
                  break;
              }
              default: {
                  throw new Exception("Indexing non-indexed type");
              }
            }
        }

    }

    internal abstract class DirectReferenceVisitor : ReferenceVisitor
    {

        [Inline]
        internal abstract unsafe void Visit(UIntPtr *location);

    }

    // This visitor should be used in concurrent settings.
    internal abstract class MutableReferenceVisitor : DirectReferenceVisitor
    {

#region HELP_DEVIRT
        // TODO: Evaluate the performance impact of these [Inline] annotations,
        // which appeared as part of the CoCo code dump.

        // This method simply forces the compiler to generate a copy
        // of VisitReferenceFieldsTemplate in this class.
        [Inline]
        [ManualRefCounts]
        internal override UIntPtr VisitReferenceFields(Object obj)
        {
            return this.VisitReferenceFields(Magic.addressOf(obj),
                                             obj.vtable);
        }

        // This method simply forces the compiler to generate a copy
        // of VisitReferenceFieldsTemplate in this class.
        [Inline]
        [ManualRefCounts]
        internal override UIntPtr VisitReferenceFields(UIntPtr objectBase,
                                                       VTable vtable)
        {
            ObjectDescriptor objDesc =
                new ObjectDescriptor(vtable, objectBase);
            return VisitReferenceFieldsTemplate(ref objDesc);
        }
#endregion

        [Inline]
        protected override unsafe
        void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
        {
            this.Visit(location);
        }

    }

    // This visitor should only be used in situations where the
    // reference fields are known to not be modified by other threads
    // while the visitor is traversing the object.
    internal abstract class NonNullReferenceVisitor : DirectReferenceVisitor
    {

#region HELP_DEVIRT
        // This method simply forces the compiler to generate a copy
        // of VisitReferenceFieldsTemplate in this class.
        [ManualRefCounts]
        [Inline]
        internal override UIntPtr VisitReferenceFields(Object obj)
        {
            return this.VisitReferenceFields(Magic.addressOf(obj),
                                             obj.vtable);
        }

        // This method simply forces the compiler to generate a copy
        // of VisitReferenceFieldsTemplate in this class.
        [ManualRefCounts]
        [Inline]
        internal override UIntPtr VisitReferenceFields(UIntPtr objectBase,
                                                       VTable vtable)
        {
            ObjectDescriptor objDesc =
                new ObjectDescriptor(vtable, objectBase);
            return VisitReferenceFieldsTemplate(ref objDesc);
        }
#endregion

        [Inline]
        protected override unsafe
        void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
        {
            if (*location != UIntPtr.Zero) {
                this.Visit(location);
            }
        }

    }

    internal abstract class OffsetReferenceVisitor : ReferenceVisitor
    {

        internal abstract void FieldOffset(UIntPtr offset,
                                           ref ObjectDescriptor objDesc);

#region HELP_DEVIRT
        // This method simply forces the compiler to generate a copy
        // of VisitReferenceFieldsTemplate in this class.
        [ManualRefCounts]
        internal override sealed
        UIntPtr VisitReferenceFields(UIntPtr objectBase, VTable vtable)
        {
            ObjectDescriptor objDesc =
                new ObjectDescriptor(vtable, objectBase);
            return VisitReferenceFieldsTemplate(ref objDesc);
        }
#endregion

        [Inline]
        protected override unsafe sealed
        void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
        {
            UIntPtr offset = ((UIntPtr) location) - objDesc.objectBase;
            this.FieldOffset(offset, ref objDesc);
        }

    }

}

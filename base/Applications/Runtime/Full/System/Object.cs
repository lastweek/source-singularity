// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Object
//
// Object is the root class for all CLR objects.  This class
// defines only the basics.
//
//===========================================================  

namespace System
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using CultureInfo = System.Globalization.CultureInfo;
    using System.Threading;

    using Microsoft.Bartok.Runtime;

    // The Object is the root class for all object in the CLR System. Object
    // is the super class for all other CLR objects and provide a set of methods and low level
    // services to subclasses.  These services include object synchronization and support for clone
    // operations.
    //
    //| <include path='docs/doc[@for="Object"]/*' />
    [AccessedByRuntime("Accessed from halexn.cpp")]
    public partial class Object
    {
        internal PreHeader preHeader;
        [AccessedByRuntime("Accessed from halexn.cpp")]
        internal PostHeader postHeader;

        // Allow us to pretend that the vtable field lives directly in Object.
        internal extern VTable vtable {
            [NoHeapAllocation]
                [Inline]
                get;
            [NoHeapAllocation]
                [Inline]
                set;
        }

        internal unsafe extern UIntPtr* VTableFieldAddr {
            [NoHeapAllocation]
                get;
        }

#if REFERENCE_COUNTING_GC
      internal uint REF_STATE {
          [Inline]
          [ManualRefCounts]
          [NoHeapAllocation]
          get {
              return this.postHeader.refState;
          }
          [Inline]
          [ManualRefCounts]
          [NoHeapAllocation]
          set {
              this.postHeader.refState = value;
          }
      }
#else // REFERENCE_COUNTING_GC
      internal uint REF_STATE {
          [NoHeapAllocation]
          [Inline]
          get {
              return 1;
          }
          [NoHeapAllocation]
          [Inline]
          set {
          }
      }
#endif

        // Creates a new instance of an Object.
        //| <include path='docs/doc[@for="Object.Object"]/*' />
        [Inline]
        public Object()
        {
        }

        // Returns a String which represents the object instance.  The default
        // for an object is to return the fully qualified name of the class.
        //
        //| <include path='docs/doc[@for="Object.ToString"]/*' />
        public virtual String ToString()
        {
            return GetType().FullName;
        }

        //| <include path='docs/doc[@for="Object.Equals1"]/*' />
        public static bool Equals(Object objA, Object objB) {
            if (objA == objB) {
                return true;
            }
            if (objA == null || objB == null) {
                return false;
            }
            return objA.Equals(objB);
        }

        //| <include path='docs/doc[@for="Object.ReferenceEquals"]/*' />
        public static bool ReferenceEquals (Object objA, Object objB) {
            return objA == objB;
        }

        // GetHashCode is intended to serve as a hash function for this object.
        // Based on the contents of the object, the hash function will return a suitable
        // value with a relatively random distribution over the various inputs.
        //
        // The default implementation returns the sync block index for this instance.
        // Calling it on the same object multiple times will return the same value, so
        // it will technically meet the needs of a hash function, but it's pretty lame.
        // Objects (& especially value classes) should override this method.
        //
        //| <include path='docs/doc[@for="Object.GetHashCode"]/*' />
        public virtual int GetHashCode()
        {
            return MultiUseWord.GetHashCode(this);
        }

        /// <summary>
        /// Test and set the state of the GC mark bit to be the same
        /// as the passed flag. Note that this operation is not
        /// synchronized so it is possible for multiple marking threads
        /// to 'mark' the same object.
        /// </summary>
        [NoHeapAllocation]
        internal unsafe bool GcMark(UIntPtr flag) {
            UIntPtr *loc = this.VTableFieldAddr;
            UIntPtr val = *loc;
            VTable.Deny(val == UIntPtr.Zero);

            if ((val & (UIntPtr)3) != flag) {
                *loc = (val & ~(UIntPtr)3) + flag;
                return true;
            }
            return false;
        }

        /// <summary>
        /// Return the current state of the GC mark bit.
        /// </summary>
        [NoHeapAllocation]
        internal unsafe UIntPtr GcMark() {
            UIntPtr *loc = this.VTableFieldAddr;
            UIntPtr val = *loc;
            return (val & 3);
        }

        internal unsafe VTable GcUnmarkedVTable {
            [Inline]
            [NoHeapAllocation]
            get {
                UIntPtr *loc = this.VTableFieldAddr;
                return Magic.toVTable(Magic.fromAddress(~(UIntPtr)3 & *loc));
            }
        }

        // Returns a Type object which represent this object instance.
        //
        //| <include path='docs/doc[@for="Object.GetType"]/*' />
        [NoHeapAllocation]
        public Type GetType()
        {
            return vtable.vtableType;
        }

        [NoHeapAllocation]
        public virtual TypeCode GetTypeCode()
        {
            return TypeCode.Object;
        }

        // Returns a new object instance that is a memberwise copy of this
        // object.  This is always a shallow copy of the instance. The method is protected
        // so that other object may only call this method on themselves.  It is intended to
        // support the ICloneable interface.
        //
        //| <include path='docs/doc[@for="Object.MemberwiseClone"]/*' />
        // BUGBUG: maybe we can try harder to mess up the GC?
        protected Object MemberwiseClone()
        {
            if (this is String) {
                return this;
                // REVIEW: ok, but what in the world is the CLR doing?
            }
            Thread thread = Thread.CurrentThread;
            if (this is Array) {
                Array srcArray = (Array) this;
                Array cloneArray;
                int srcLength = srcArray.Length;
                if (srcArray.IsVector) {
                    cloneArray = GC.AllocateVector(srcArray.vtable, srcLength);
                    CloneVectorContents(srcArray, cloneArray);
                }
                else {
                    int rank = srcArray.Rank;
                    cloneArray =
                        GC.AllocateArray(srcArray.vtable, rank, srcLength);
                    CloneArrayContents(srcArray, cloneArray);
                }
                return cloneArray;
            }
            else {
                Object clone = GC.AllocateObject(this.vtable);
                CloneObjectContents(this, clone);
                return clone;
            }
        }

#if !REFERENCE_COUNTING_GC && !DEFERRED_REFERENCE_COUNTING_GC

      private unsafe static void CloneObjectContents(Object src, Object dst)
      {
          System.GCs.Barrier.Clone(src, dst);
      }

      private unsafe static void CloneVectorContents(Array srcArray,
                                                     Array dstArray)
      {
          System.GCs.Barrier.Clone(srcArray, dstArray);
      }

      private unsafe static void CloneArrayContents(Array srcArray,
                                                    Array dstArray)
      {
          System.GCs.Barrier.Clone(srcArray, dstArray);
      }

#else

        private unsafe static void CloneObjectContents(Object src, Object dst)
        {
            byte * dstNOTFIXED = (byte *)(Magic.addressOf(dst) + PostHeader.Size);
            byte * srcNOTFIXED = (byte *)(Magic.addressOf(src) + PostHeader.Size);
            int size = unchecked((int) src.vtable.baseLength);
            // We don't copy the header fields, the vtable or the RS field!
            size -= (PreHeader.Size + PostHeader.Size);
#if REFERENCE_COUNTING_GC
            GCs.ReferenceCountingCollector.
                IncrementReferentRefCounts(Magic.addressOf(src), src.vtable);
            GCs.ReferenceCountingCollector.
                DecrementReferentRefCounts(Magic.addressOf(dst), dst.vtable);
#elif DEFERRED_REFERENCE_COUNTING_GC
            GCs.DeferredReferenceCountingCollector.
                IncrementReferentRefCounts(Magic.addressOf(src), src.vtable);
            GCs.DeferredReferenceCountingCollector.
                DecrementReferentRefCounts(Magic.addressOf(dst), dst.vtable);
#endif // REFERENCE_COUNTING_GC
            Buffer.MoveMemory(dstNOTFIXED,srcNOTFIXED,size);
        }

        private unsafe static void CloneVectorContents(Array srcArray,
                                                       Array dstArray)
        {
            int srcLength = srcArray.Length;
            fixed (int *srcFieldPtr = &srcArray.field1) {
                fixed (int *dstFieldPtr = &dstArray.field1) {
                    byte *srcDataPtr = (byte *)
                        srcArray.GetFirstElementAddress(srcFieldPtr);
                    byte *dstDataPtr = (byte *)
                        dstArray.GetFirstElementAddress(dstFieldPtr);
                    int size = srcArray.vtable.arrayElementSize * srcLength;
                    Buffer.MoveMemory(dstDataPtr, srcDataPtr, size);
                }
            }
        }

        private unsafe static void CloneArrayContents(Array srcArray,
                                                      Array dstArray)
        {
            int srcLength = srcArray.Length;
            fixed (int *srcFieldPtr = &srcArray.field1) {
                fixed (int *dstFieldPtr = &dstArray.field1) {
                    byte *srcDataPtr = (byte *)
                        srcArray.GetFirstElementAddress(srcFieldPtr);
                    byte *dstDataPtr = (byte *)
                        dstArray.GetFirstElementAddress(dstFieldPtr);
                    byte *srcDimPtr = (byte *)
                        srcArray.GetFirstDimInfoRectangleArray();
                    int dimInfoSize = (int) (srcDataPtr - srcDimPtr);
                    int size = srcArray.vtable.arrayElementSize * srcLength;
                    Buffer.MoveMemory(dstDataPtr - dimInfoSize,
                                      srcDataPtr - dimInfoSize,
                                      size + dimInfoSize);
                }
            }
        }

#endif

    }
}

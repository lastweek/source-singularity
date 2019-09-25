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
    public class Object
    {
        internal PreHeader preHeader;
        [AccessedByRuntime("Accessed from halexn.cpp")]
        internal PostHeader postHeader;

        // Allow us to pretend that the vtable field lives directly in Object.
        internal VTable vtable {
            [NoHeapAllocation]
                [Inline]
                get { return postHeader.vtableObject; }
        }

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

        [RequiredByBartok]
        public virtual bool Equals(Object obj) {
            return this == obj;
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
            return 0; // TODO MultiUseWord.GetHashCode(this);
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

/*TODO
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

      private static void CloneObjectContents(Object src, Object dst)
      {
          System.GCs.Barrier.Clone(src, dst);
      }

      private static void CloneVectorContents(Array srcArray,
                                                     Array dstArray)
      {
          System.GCs.Barrier.Clone(srcArray, dstArray);
      }

      private static void CloneArrayContents(Array srcArray,
                                                    Array dstArray)
      {
          System.GCs.Barrier.Clone(srcArray, dstArray);
      }
*/
    }
}

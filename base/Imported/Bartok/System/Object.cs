// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*============================================================
**
** Class:  Object
**
** Object is the root class for all CLR objects.  This class
** defines only the basics.
**
===========================================================*/

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
    [NoCCtor]
    public partial class Object
    {
        // Returns a boolean indicating if the passed in object obj is
        // Equal to this.  Equality is defined as object equality for reference
        // types and bitwise equality for value types using a loader trick to
        // replace Equals with EqualsValue for value types).
        //
        //| <include path='docs/doc[@for="Object.Equals"]/*' />
        [RequiredByBartok]
        public virtual bool Equals(Object obj)
        {
            // This method is overridden for value types
            return (this == obj);
        }

        // Allow an object to free resources before the object is reclaimed by the GC.
        // Note: This defines a protected method called Finalize.
        //| <include path='docs/doc[@for="Object.Finalize"]/*' />
        [RequiredByBartok]
        ~Object()
        {
        }
    }
}

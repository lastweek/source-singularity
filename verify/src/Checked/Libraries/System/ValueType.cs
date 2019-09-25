// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:   ValueType
//
// Purpose: Base class for all value classes.
//
//===========================================================  
namespace System
{
    using System;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="ValueType"]/*' />
    [NoCCtor]
    public abstract class ValueType {

        //| <include path='docs/doc[@for="ValueType.Equals"]/*' />
        public override bool Equals (Object obj) {
            throw new Exception("System.ValueType.Equals not implemented in Bartok!");
        }

        //=================================GetHashCode==================================
        //Action: Our algorithm for returning the hashcode is a little bit complex.  We look
        //        for the first non-static field and get its hashcode.  If the type has no
        //        non-static fields, we return the hashcode of the type.  We can't take the
        //        hashcode of a static member because if that member is of the same type as
        //        the original type, we'll end up in an infinite loop.
        //Returns: The hashcode for the type.
        //Arguments: None.
        //Exceptions: None.
        //==============================================================================  
        //| <include path='docs/doc[@for="ValueType.GetHashCode"]/*' />
        public override int GetHashCode() {
            throw new Exception("System.ValueType.GetHashCode not implemented in Bartok!");
        }

        //| <include path='docs/doc[@for="ValueType.ToString"]/*' />
        public override String ToString() {
            Type thisType = this.GetType();
            return thisType.FullName;
        }
    }
}

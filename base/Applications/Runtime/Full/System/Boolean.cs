// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Boolean
//
// Purpose: The boolean class serves as a wrapper for the primitive
// type boolean.
//
//===========================================================  
namespace System
{

    using System;
    using System.Globalization;
    using System.Runtime.CompilerServices;

    // The Boolean class provides the
    // object representation of the boolean primitive type.
    //| <include path='docs/doc[@for="Boolean"]/*' />
    public struct Boolean : IComparable {

        //
        // Member Variables
        //
        private bool m_value;


        //
        // Public Constants
        //

        // The true value.
        //
        internal const int True = 1;

        // The false value.
        //
        internal const int False = 0;

        // The string representation of true.
        //
        //| <include path='docs/doc[@for="Boolean.TrueString"]/*' />
        public static readonly String TrueString  = "True";

        // The string representation of false.
        //
        //| <include path='docs/doc[@for="Boolean.FalseString"]/*' />
        public static readonly String FalseString = "False";

        //
        // Overridden Instance Methods
        //
        //=================================GetHashCode==================================
        //Args:  None
        //Returns: 1 or 0 depending on whether this instance represents true or false.
        //Exceptions: None
        //Overridden From: Value
        //==============================================================================  
        // Provides a hash code for this instance.
        //| <include path='docs/doc[@for="Boolean.GetHashCode"]/*' />
        public override int GetHashCode() {
            return (m_value)?True:False;
        }

        //===================================ToString===================================
        //Args: None
        //Returns:  "True" or "False" depending on the state of the boolean.
        //Exceptions: None.
        //==============================================================================  
        // Converts the boolean value of this instance to a String.
        //| <include path='docs/doc[@for="Boolean.ToString"]/*' />
        public override String ToString() {
            if (false == m_value) {
                return FalseString;
            }
            return TrueString;
        }

        // Determines whether two Boolean objects are equal.
        //| <include path='docs/doc[@for="Boolean.Equals"]/*' />
        public override bool Equals (Object obj) {
            //If it's not a boolean, we're definitely not equal
            if (!(obj is Boolean)) {
                return false;
            }

            return (m_value==((Boolean)obj).m_value);
        }

        // Compares this object to another object, returning an integer that
        // indicates the relationship. For booleans, false sorts before true.
        // null is considered to be less than any instance.
        // If object is not of type boolean, this method throws an ArgumentException.
        //
        // Returns a value less than zero if this  object
        //
        //| <include path='docs/doc[@for="Boolean.CompareTo"]/*' />
        public int CompareTo(Object obj) {
            if (obj == null) {
                return 1;
            }
            if (!(obj is Boolean)) {
                throw new ArgumentException ("Arg_MustBeBoolean");
            }

            if (m_value ==((Boolean)obj).m_value) {
                return 0;
            }
            else if (m_value == false) {
                return -1;
            }
            return 1;

        }

        //
        // Static Methods
        //

        // Determines whether a String represents true or false.
        //
        //| <include path='docs/doc[@for="Boolean.Parse"]/*' />
        public static bool Parse(String value) {
            if (value==null) throw new ArgumentNullException("value");
            // For perf reasons, let's first see if they're equal, then do the
            // trim to get rid of white space, and check again.
            if (0 == String.Compare(value, TrueString,true))
                return true;
            if (0 == String.Compare(value,FalseString,true))
                return false;

            value = value.Trim();  // Remove leading & trailing white space.
            if (0 == String.Compare(value, TrueString,true))
                return true;
            if (0 == String.Compare(value,FalseString,true))
                return false;
            throw new FormatException("Format_BadBoolean");
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Boolean.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode() {
            return TypeCode.Boolean;
        }

        //
        // This is just designed to prevent compiler warnings.
        // This field is used from native, but we need to prevent the compiler warnings.
        //
#if _DEBUG
        private void DontTouchThis() {
            m_value = m_value;
        }
#endif
    }
}

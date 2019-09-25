// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Interface:  IComparer
//
// Purpose: Interface for comparing two Objects.
//
//===========================================================  
namespace System.Collections
{

    using System;
    // The IComparer interface implements a method that compares two objects. It is
    // used in conjunction with the Sort and BinarySearch methods on
    // the Array and List classes.
    //
    //| <include path='docs/doc[@for="IComparer"]/*' />
    public interface IComparer {
        // Compares two objects. An implementation of this method must return a
        // value less than zero if x is less than y, zero if x is equal to y, or a
        // value greater than zero if x is greater than y.
        //
        //| <include path='docs/doc[@for="IComparer.Compare"]/*' />
        int Compare(Object x, Object y);
    }
}

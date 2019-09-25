// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Interface: IHashCodeProvider
//
// Purpose: A bunch of strings.
//
//===========================================================  
namespace System.Collections
{

    using System;
    // Provides a mechanism for a hash table user to override the default
    // GetHashCode() function on Objects, providing their own hash function.
    //| <include path='docs/doc[@for="IHashCodeProvider"]/*' />
    public interface IHashCodeProvider
    {
        // Returns a hash code for the given object.
        //
        //| <include path='docs/doc[@for="IHashCodeProvider.GetHashCode"]/*' />
        int GetHashCode (Object obj);
    }
}

// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Interface:  IDictionary
//
// Purpose: Base interface for all dictionarys.
//
//===========================================================  
namespace System.Collections
{
    using System;

    // An IDictionary is a possibly unordered set of key-value pairs.
    // Keys can be any non-null object.  Values can be any object.
    // You can look up a value in an IDictionary via the default indexed
    // property, Items.
    //| <include path='docs/doc[@for="IDictionary"]/*' />
    public interface IDictionary : ICollection
    {
        //| <include path='docs/doc[@for="IDictionary.this"]/*' />

        // The Item property provides methods to read and edit entries
        // in the Dictionary.
        Object this[Object key] {
            get;
            set;
        }

        // Returns a collections of the keys in this dictionary.
        //| <include path='docs/doc[@for="IDictionary.Keys"]/*' />
        ICollection Keys {
            get;
        }

        // Returns a collections of the values in this dictionary.
        //| <include path='docs/doc[@for="IDictionary.Values"]/*' />
        ICollection Values {
            get;
        }

        // Returns whether this dictionary contains a particular key.
        //
        //| <include path='docs/doc[@for="IDictionary.Contains"]/*' />
        bool Contains(Object key);

        // Adds a key-value pair to the dictionary.
        //
        //| <include path='docs/doc[@for="IDictionary.Add"]/*' />
        void Add(Object key, Object value);

        // Removes all pairs from the dictionary.
        //| <include path='docs/doc[@for="IDictionary.Clear"]/*' />
        void Clear();
        //| <include path='docs/doc[@for="IDictionary.IsReadOnly"]/*' />

        bool IsReadOnly
        { get; }
        //| <include path='docs/doc[@for="IDictionary.IsFixedSize"]/*' />

        bool IsFixedSize
        { get; }

        // Returns an IDictionaryEnumerator for this dictionary.
        //| <include path='docs/doc[@for="IDictionary.GetEnumerator"]/*' />
        new IDictionaryEnumerator GetEnumerator();

        // Removes a particular key from the dictionary.
        //
        //| <include path='docs/doc[@for="IDictionary.Remove"]/*' />
        void Remove(Object key);
    }
}

// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Runtime.CompilerServices
{
    using System;

    //| <include path='docs/doc[@for="IndexerNameAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Property, Inherited = true)]
    public sealed class IndexerNameAttribute: Attribute
    {
        //| <include path='docs/doc[@for="IndexerNameAttribute.IndexerNameAttribute"]/*' />
        public IndexerNameAttribute(String indexerName)
        {}
    }
}

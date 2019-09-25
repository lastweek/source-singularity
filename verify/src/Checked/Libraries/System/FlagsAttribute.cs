// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
namespace System
{

    using System;
    // Custom attribute to indicate that the enum
    // should be treated as a bitfield (or set of flags).
    // An IDE may use this information to provide a richer
    // development experience.
    //| <include path='docs/doc[@for="FlagsAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Enum, Inherited = false)]
    public class  FlagsAttribute : Attribute
    {
        //| <include path='docs/doc[@for="FlagsAttribute.FlagsAttribute"]/*' />
        public FlagsAttribute()
        {
        }
    }
}

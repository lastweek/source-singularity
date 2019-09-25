// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Runtime.CompilerServices
{

    using System;


    // This Enum matches the miImpl flags defined in corhdr.h. It is used to specify
    // certain method properties.

    //| <include path='docs/doc[@for="MethodImplOptions"]/*' />
    [Flags]
    public enum MethodImplOptions
    {
        //| <include path='docs/doc[@for="MethodImplOptions.Unmanaged"]/*' />
        Unmanaged       =   0x0004,
        //| <include path='docs/doc[@for="MethodImplOptions.ForwardRef"]/*' />
        ForwardRef      =   0x0010,
        //| <include path='docs/doc[@for="MethodImplOptions.InternalCall"]/*' />
        InternalCall    =   0x1000,
        //| <include path='docs/doc[@for="MethodImplOptions.Synchronized"]/*' />
        Synchronized    =   0x0020,
        //| <include path='docs/doc[@for="MethodImplOptions.NoInlining"]/*' />
        NoInlining      =   0x0008,
    }

    // Custom attribute to specify additional method properties.
    //| <include path='docs/doc[@for="MethodImplAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Method | AttributeTargets.Constructor, Inherited = false)]
    sealed public class MethodImplAttribute : Attribute
    {
        internal MethodImplOptions  _val;

        //| <include path='docs/doc[@for="MethodImplAttribute.MethodImplAttribute"]/*' />
        public MethodImplAttribute(MethodImplOptions methodImplOptions)
        {
            _val = methodImplOptions;
        }
        //| <include path='docs/doc[@for="MethodImplAttribute.MethodImplAttribute1"]/*' />
        public MethodImplAttribute(short value)
        {
            _val = (MethodImplOptions)value;
        }
        //| <include path='docs/doc[@for="MethodImplAttribute.MethodImplAttribute2"]/*' />
        public MethodImplAttribute()
        {
        }

        //| <include path='docs/doc[@for="MethodImplAttribute.Value"]/*' />
        public MethodImplOptions Value { get {return _val;} }
    }

}

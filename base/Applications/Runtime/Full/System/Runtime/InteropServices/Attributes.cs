// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
namespace System.Runtime.InteropServices
{

    using System;

    //| <include path='docs/doc[@for="GuidAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Assembly | AttributeTargets.Interface | AttributeTargets.Class | AttributeTargets.Enum | AttributeTargets.Struct | AttributeTargets.Delegate, Inherited = false)]
    public sealed class GuidAttribute : Attribute
    {
        internal String _val;
        //| <include path='docs/doc[@for="GuidAttribute.GuidAttribute"]/*' />
        public GuidAttribute(String guid)
        {
            _val = guid;
        }
        //| <include path='docs/doc[@for="GuidAttribute.Value"]/*' />
        public String Value { get {return _val;} }
    }

    //| <include path='docs/doc[@for="InAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Parameter, Inherited = false)]
    public sealed class InAttribute : Attribute
    {
        //| <include path='docs/doc[@for="InAttribute.InAttribute"]/*' />
        public InAttribute()
        {
        }
    }

    //| <include path='docs/doc[@for="OutAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Parameter, Inherited = false)]
    public sealed class OutAttribute : Attribute
    {
        //| <include path='docs/doc[@for="OutAttribute.OutAttribute"]/*' />
        public OutAttribute()
        {
        }
    }

    //| <include path='docs/doc[@for="OptionalAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Parameter, Inherited = false)]
    public sealed class OptionalAttribute : Attribute
    {
        //| <include path='docs/doc[@for="OptionalAttribute.OptionalAttribute"]/*' />
        public OptionalAttribute()
        {
        }
    }

    //| <include path='docs/doc[@for="StructLayoutAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Class | AttributeTargets.Struct, Inherited = false)]
    public sealed class StructLayoutAttribute : Attribute
    {
        internal LayoutKind _val;
        //| <include path='docs/doc[@for="StructLayoutAttribute.StructLayoutAttribute"]/*' />
        public StructLayoutAttribute(LayoutKind layoutKind)
        {
            _val = layoutKind;
        }
        //| <include path='docs/doc[@for="StructLayoutAttribute.StructLayoutAttribute1"]/*' />
        public StructLayoutAttribute(short layoutKind)
        {
            _val = (LayoutKind)layoutKind;
        }
        //| <include path='docs/doc[@for="StructLayoutAttribute.Value"]/*' />
        public LayoutKind Value { get {return _val;} }
        //| <include path='docs/doc[@for="StructLayoutAttribute.Pack"]/*' />
        public int                Pack;
        //| <include path='docs/doc[@for="StructLayoutAttribute.Size"]/*' />
        public int            Size;
        //| <include path='docs/doc[@for="StructLayoutAttribute.CharSet"]/*' />
        public CharSet	      CharSet;
    }

    //| <include path='docs/doc[@for="FieldOffsetAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Field, Inherited = false)]
    public sealed class FieldOffsetAttribute : Attribute
    {
        internal int _val;
        //| <include path='docs/doc[@for="FieldOffsetAttribute.FieldOffsetAttribute"]/*' />
        public FieldOffsetAttribute(int offset)
        {
            _val = offset;
        }
        //| <include path='docs/doc[@for="FieldOffsetAttribute.Value"]/*' />
        public int Value { get {return _val;} }
    }

}

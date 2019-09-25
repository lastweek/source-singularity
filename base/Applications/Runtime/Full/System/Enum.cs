// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{
    using System.Diagnostics;
    using System.Reflection;
    using System.Runtime.CompilerServices;
    using Microsoft.Bartok.Runtime;

    //| <include path='docs/doc[@for="Enum"]/*' />
    public abstract class Enum : ValueType, IComparable, IFormattable
    {
        //| <include path='docs/doc[@for="Enum.Equals"]/*' />
        public override bool Equals(Object obj)
        {
            Enum that = obj as Enum;
            if (that == null || this.GetType() != obj.GetType())
                return false;
            return this.GetValue().Equals(that.GetValue());
        }

        //| <include path='docs/doc[@for="Enum.GetHashCode"]/*' />
        public override int GetHashCode()
        {
            return GetValue().GetHashCode();
        }

        // Compares this enum and the object.
        // They have to be of the same type or a ArgumentException is thrown
        // Returns 0 if equal, -1 if less than, or 1 greater then the target
        //| <include path='docs/doc[@for="Enum.CompareTo"]/*' />
        public int CompareTo(Object target)
        {
            return ((IComparable)GetValue()).CompareTo(target);
        }

        //| <include path='docs/doc[@for="Enum.ToString"]/*' />
        public String ToString(String format)
        {
            return ((IFormattable)GetValue()).ToString(format);
        }

        public override String ToString()
        {
            return GetValue().ToString();
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Enum.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode()
        {
            StructuralType type = this.vtable.structuralView;

            switch (type) {
                case StructuralType.Int8:
                    return TypeCode.SByte;
                case StructuralType.Int16:
                    return TypeCode.Int16;
                case StructuralType.Int32:
                    return TypeCode.Int32;
                case StructuralType.Int64:
                    return TypeCode.Int64;
                case StructuralType.UInt8:
                    return TypeCode.Byte;
                case StructuralType.UInt16:
                    return TypeCode.UInt16;
                case StructuralType.UInt32:
                    return TypeCode.UInt32;
                case StructuralType.UInt64:
                    return TypeCode.UInt64;
                default:
                    VTable.NotReached("bad enum in InternalGetValue");
                    return TypeCode.Object;
            }
        }

        private Object GetValue()
        {
            StructuralType type = this.vtable.structuralView;
            Object result;

            switch (type) {
                case StructuralType.Int8:
                    result = (sbyte) (Object) this;
                    break;
                case StructuralType.Int16:
                    result = (short) (Object) this;
                    break;
                case StructuralType.Int32:
                    result = (int) (Object) this;
                    break;
                case StructuralType.Int64:
                    result = (long) (Object) this;
                    break;
                case StructuralType.UInt8:
                    result = (byte) (Object) this;
                    break;
                case StructuralType.UInt16:
                    result = (ushort) (Object) this;
                    break;
                case StructuralType.UInt32:
                    result = (uint) (Object) this;
                    break;
                case StructuralType.UInt64:
                    result = (ulong) (Object) this;
                    break;
                default:
                    VTable.NotReached("bad enum in InternalGetValue");
                    result = null;
                    break;
            }
            return result;
        }
    }
}





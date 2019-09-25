// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// __RuntimeType is the basic Type object representing classes as found in the
//      system.  This type is never creatable by users, only by the system itself.
//      The internal structure is known about by the runtime. __RuntimeXXX classes
//      are created only once per object in the system and support == comparisons.
//

namespace System
{

    using Microsoft.Bartok.Runtime;
    using System;
    using System.Reflection;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using System.Text;
    using Thread = System.Threading.Thread;
    using SystemType = Microsoft.Singularity.V1.Types.SystemType;

    internal sealed partial class RuntimeType : Type
    {
        public override int GetHashCode() {
            return ((int)this.classVtable.arrayOf << 8 + rank)
                + (int)this.classVtable.structuralView;
        }

        // Return the name of the class.  The name does not contain the namespace.
        public override String ToString(){
            return InternalGetProperlyQualifiedName();
        }

        private String InternalGetProperlyQualifiedName() {
            // See also Lightning\Src\VM\COMClass.cpp::GetProperName
            return FullName;
        }

        // GetInterfacesInternal
        // A version of GetInterfaces to be used by trusted code.   It does not
        // copy the array before returning it.

        protected Type[] GetInterfacesInternal() {
            return this.interfaces;
        }

        ////////////////////////////////////////////////////////////////////////////////
        //
        // Attributes
        //
        //   The attributes are all treated as read-only properties on a class.  Most of
        //  these boolean properties have flag values defined in this class and act like
        //  a bit mask of attributes.  There are also a set of boolean properties that
        //  relate to the classes relationship to other classes and to the state of the
        //  class inside the runtime.
        //
        ////////////////////////////////////////////////////////////////////////////////

        [NoHeapAllocation]
        protected override bool HasElementTypeImpl()
        {
            return (IsArray);
        }

        // Return the underlying Type that represents the IReflect Object.  For expando object,
        // this is the (Object) IReflectInstance.GetType().  For Type object it is this.
        public override Type UnderlyingSystemType {
            [NoHeapAllocation]
            get {return this;}
        }

        [NoHeapAllocation]
        internal override TypeCode GetTypeCodeInternal()
        {
            switch (classVtable.structuralView) {
                case StructuralType.Bool:
                    return TypeCode.Boolean;
                case StructuralType.Char:
                    return TypeCode.Object;
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
                case StructuralType.Float32:
                    return TypeCode.Single;
                case StructuralType.Float64:
                    return TypeCode.Double;
                default:
                    return TypeCode.Object;
            }
        }

        public override SystemType GetSystemType() {
            if (SystemType.IsNull(this.systemType)) {
                // initialize it
                if (this.baseType == null) {
                    this.systemType = SystemType.RootSystemType();
                }
                else {
                    SystemType baseSt = this.baseType.GetSystemType();
                    long lower, upper;
                    string fullname = this.FullName;
                    // for now compute an MD5 over the full name

#if SINGULARITY_PROCESS
                    unsafe {
                        byte[] nameArray =
                            RuntimeTypeHash.ComputeHashAndReturnName(fullname,
                                                                     out lower,
                                                                     out upper);
                        fixed(byte* dataptr = &nameArray[0]) {
                            char* name = (char*)dataptr;
                            this.systemType = SystemType.Register(name,
                                                                  fullname.Length,
                                                                  lower, upper, baseSt);
                        }
                    }
#else
                    RuntimeTypeHash.ComputeHash(fullname, out lower, out upper);
                    this.systemType = SystemType.Register(fullname,
                                                          lower,
                                                          upper,
                                                          baseSt);
#endif
                }
            }
            return this.systemType;
        }

    }


    // Pulled these methods out of the main class in order to give
    // the IoSystem access to the ComputeHash function when prebinding endpoints
    public class RuntimeTypeHash
    {
        public static void ComputeHash(string fullname,
                                       out long lower,
                                       out long upper)
        {
            ComputeHashAndReturnName(fullname, out lower, out upper);
        }

        unsafe internal static byte[] ComputeHashAndReturnName(string fullname,
                                                               out long lower,
                                                               out long upper)
        {
            byte[] data = new byte[fullname.Length*sizeof(char)];
            String.InternalCopy(fullname, data, fullname.Length);
            ComputeHash(data, out lower, out upper);
            return data;
        }
        ///
        ///  Needs to be replaced with real hash computed over the
        ///  signature of the type
        ///
        unsafe internal static void ComputeHash(byte[] fullname,
                                              out long lower,
                                              out long upper)
        {
            byte[] md5 = new Microsoft.Singularity.Crypto.MD5().Hash(fullname);

            lower = ConvertToLong(md5, 0);
            upper = ConvertToLong(md5, 8);
        }

        private static long ConvertToLong(byte[] data, int start) {
            long result = data[start];
            for (int i = 1; i < 8; i++) {
                result = result << 8;
                result |= data[start+i];
            }
            return result;
        }
    }
}

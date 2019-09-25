// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Type is the root of all reflection and the Object that represents
//  a type inside the system.  Type is an abstract base class that allows multiple
//      implementations.  The system will always provide the subclass __RuntimeType.
//      In Reflection all of the __RuntimeXXX classes are created only once per object
//      in the system and support == comparisons.
//
namespace System
{

    using System;
    using System.Reflection;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using DebuggerStepThroughAttribute = System.Diagnostics.DebuggerStepThroughAttribute;

    //| <include path='docs/doc[@for="Type"]/*' />
    [AccessedByRuntime("C++ needs to know relationship to RuntimeType")]
    public abstract partial class Type
    {
        //| <include path='docs/doc[@for="Type.Delimiter"]/*' />
        public static readonly char Delimiter = '.';

        // Prevent from begin created, and allow subclass
        //      to create.
        //| <include path='docs/doc[@for="Type.Type"]/*' />
        protected Type() {}

        // GetTypeCode
        // This method will return a TypeCode for the passed
        //  type.
        //| <include path='docs/doc[@for="Type.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public static TypeCode GetTypeCode(Type type)
        {
            if (type == null)
                return TypeCode.Empty;
            return type.GetTypeCodeInternal();
        }

        [NoHeapAllocation]
        internal virtual TypeCode GetTypeCodeInternal()
        {
            Type type = this;

            if (type != type.UnderlyingSystemType)
                return Type.GetTypeCode(type.UnderlyingSystemType);

            return TypeCode.Object;
        }

        //| <include path='docs/doc[@for="Type.GetTypeFromHandle"]/*' />
        [Inline]
        [NoBarriers]
        [NoHeapAllocation]
        public static Type GetTypeFromHandle(RuntimeTypeHandle handle)
        {
            return RuntimeType.GetTypeFromHandleImpl(handle);
        }

        // Property representing the name of the Member.
        //| <include path='docs/doc[@for="MemberInfo.Name"]/*' />
        public abstract String Name {
            [NoHeapAllocation] get;
        }

        // Return the fully qualified name.  The name does contain the namespace.
        //| <include path='docs/doc[@for="Type.FullName"]/*' />
        public abstract String FullName {
            get;
        }

        // Return the name space of the class.
        //| <include path='docs/doc[@for="Type.Namespace"]/*' />
        public abstract String Namespace {
            [NoHeapAllocation]
            get;
        }

        public abstract Assembly Assembly {
            [NoHeapAllocation]
            get;
        }

        //| <include path='docs/doc[@for="Type.AssemblyQualifiedName"]/*' />
        public abstract String AssemblyQualifiedName {
            get;
        }

        // @TODO: Next integration make this method abstract
        //| <include path='docs/doc[@for="Type.GetArrayRank"]/*' />
        public virtual int GetArrayRank() {
            throw new NotSupportedException("NotSupported_SubclassOverride");
        }

        // Returns the base class for a class.  If this is an interface or has
        // no base class null is returned.  Object is the only Type that does not
        // have a base class.
        //| <include path='docs/doc[@for="Type.BaseType"]/*' />
        public abstract Type BaseType {
            [NoHeapAllocation]
            get;
        }


        // GetInterfaces
        // This method will return all of the interfaces implemented by a
        //  class
        //| <include path='docs/doc[@for="Type.GetInterfaces"]/*' />
        abstract public Type[] GetInterfaces();

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

        // The attribute property on the Type.
        //| <include path='docs/doc[@for="Type.Attributes"]/*' />
        public TypeAttributes Attributes     {
            [NoHeapAllocation]
            get {return GetAttributeFlagsImpl();}
        }
        //| <include path='docs/doc[@for="Type.IsNotPublic"]/*' />
        public bool IsNotPublic {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.VisibilityMask) == TypeAttributes.NotPublic);}
        }
        //| <include path='docs/doc[@for="Type.IsPublic"]/*' />
        public bool IsPublic {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.VisibilityMask) == TypeAttributes.Public);}
        }
        //| <include path='docs/doc[@for="Type.IsNestedPublic"]/*' />
        public bool IsNestedPublic {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.VisibilityMask) == TypeAttributes.NestedPublic);}
        }
        //| <include path='docs/doc[@for="Type.IsNestedPrivate"]/*' />
        public bool IsNestedPrivate {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.VisibilityMask) == TypeAttributes.NestedPrivate);}
        }
        //| <include path='docs/doc[@for="Type.IsNestedFamily"]/*' />
        public bool IsNestedFamily {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.VisibilityMask) == TypeAttributes.NestedFamily);}
        }
        //| <include path='docs/doc[@for="Type.IsNestedFamANDAssem"]/*' />
        public bool IsNestedFamANDAssem {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.VisibilityMask) == TypeAttributes.NestedFamANDAssem);}
        }
        //| <include path='docs/doc[@for="Type.IsNestedFamORAssem"]/*' />
        public bool IsNestedFamORAssem{
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.VisibilityMask) == TypeAttributes.NestedFamORAssem);}
        }

        //| <include path='docs/doc[@for="Type.IsAutoLayout"]/*' />
        public bool IsAutoLayout {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.LayoutMask) == TypeAttributes.AutoLayout);}
        }
        //| <include path='docs/doc[@for="Type.IsLayoutSequential"]/*' />
        public bool IsLayoutSequential {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.LayoutMask) == TypeAttributes.SequentialLayout);}
        }
        //| <include path='docs/doc[@for="Type.IsExplicitLayout"]/*' />
        public bool IsExplicitLayout {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout);}
        }

        //| <include path='docs/doc[@for="Type.IsClass"]/*' />
        public bool IsClass {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.ClassSemanticsMask) == TypeAttributes.Class && !IsSubclassOf(Type.valueType));}
        }
        //| <include path='docs/doc[@for="Type.IsInterface"]/*' />
        public bool IsInterface {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.ClassSemanticsMask) == TypeAttributes.Interface);}
        }
        //| <include path='docs/doc[@for="Type.IsValueType"]/*' />
        public bool IsValueType {
            [NoHeapAllocation]
            get {return IsValueTypeImpl();}
        }

        //| <include path='docs/doc[@for="Type.IsAbstract"]/*' />
        public bool IsAbstract {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.Abstract) != 0);}
        }
        //| <include path='docs/doc[@for="Type.IsSealed"]/*' />
        public bool IsSealed {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.Sealed) != 0);}
        }
        //| <include path='docs/doc[@for="Type.IsEnum"]/*' />
        public bool IsEnum {
            [NoHeapAllocation]
            get {return IsSubclassOf(Type.enumType);}
        }
        //| <include path='docs/doc[@for="Type.IsSpecialName"]/*' />
        public bool IsSpecialName {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.SpecialName) != 0);}
        }
        //| <include path='docs/doc[@for="Type.IsImport"]/*' />
        public bool IsImport {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.Import) != 0);}
        }

        //| <include path='docs/doc[@for="Type.IsAnsiClass"]/*' />
        public bool IsAnsiClass {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.StringFormatMask) == TypeAttributes.AnsiClass);}
        }
        //| <include path='docs/doc[@for="Type.IsUnicodeClass"]/*' />
        public bool IsUnicodeClass {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.StringFormatMask) == TypeAttributes.UnicodeClass);}
        }
        //| <include path='docs/doc[@for="Type.IsAutoClass"]/*' />
        public bool IsAutoClass {
            [NoHeapAllocation]
            get {return ((GetAttributeFlagsImpl() & TypeAttributes.StringFormatMask) == TypeAttributes.AutoClass);}
        }

        // These are not backed up by attributes.  Instead they are implemented
        //      based internally.
        //| <include path='docs/doc[@for="Type.IsArray"]/*' />
        public bool IsArray {
            [NoHeapAllocation]
            get {return IsArrayImpl();}
        }

        //| <include path='docs/doc[@for="Type.IsPrimitive"]/*' />
        public bool IsPrimitive {
            [NoHeapAllocation]
            get {return IsPrimitiveImpl();}
        }
        //| <include path='docs/doc[@for="Type.HasElementType"]/*' />
        public bool HasElementType {
            [NoHeapAllocation]
            get {return HasElementTypeImpl();}
        }

        // Protected routine to determine if this class represents a value class
        //| <include path='docs/doc[@for="Type.IsValueTypeImpl"]/*' />
        [NoHeapAllocation]
        protected virtual bool IsValueTypeImpl() {
            Type type = this;
            if (type == Type.valueType || type == Type.enumType) {
                return false;
            }
            return IsSubclassOf(Type.valueType);
        }

        // Protected routine to get the attributes.
        //| <include path='docs/doc[@for="Type.GetAttributeFlagsImpl"]/*' />
        [NoHeapAllocation]
        abstract protected TypeAttributes GetAttributeFlagsImpl();

        // Protected routine to determine if this class represents an Array
        //| <include path='docs/doc[@for="Type.IsArrayImpl"]/*' />
        [NoHeapAllocation]
        abstract protected bool IsArrayImpl();

        // Protected routine to determine if this class represents a primitive type
        //| <include path='docs/doc[@for="Type.IsPrimitiveImpl"]/*' />
        [NoHeapAllocation]
        abstract protected bool IsPrimitiveImpl();

        //| <include path='docs/doc[@for="Type.GetElementType"]/*' />
        [NoHeapAllocation]
        abstract public Type GetElementType();

        //| <include path='docs/doc[@for="Type.HasElementTypeImpl"]/*' />
        [NoHeapAllocation]
        abstract protected bool HasElementTypeImpl();

        // Return the underlying Type that represents the IReflect Object.  For expando object,
        // this is the (Object) IReflectInstance.GetType().  For Type object it is this.
        //| <include path='docs/doc[@for="Type.UnderlyingSystemType"]/*' />
        public abstract Type UnderlyingSystemType {
            [NoHeapAllocation]
            get;
        }

        // Returns true if this class is a true subclass of c.  Everything
        // else returns false.  If this class and c are the same class false is
        // returned.
        //
        //| <include path='docs/doc[@for="Type.IsSubclassOf"]/*' />
        [NoHeapAllocation]
        public virtual bool IsSubclassOf(Type c)
        {
            Type p = this;
            if (p == c) {
                return false;
            }
            while (p != null) {
                if (p == c) {
                    return true;
                }
                p = p.BaseType;
            }
            return false;
        }

        // Returns true if an instance of Type c may be assigned
        // to an instance of this class.  Return false otherwise.
        // 
        //| <include file='doc\Type.uex' path='docs/doc[@for="Type.IsAssignableFrom"]/*' />
        public virtual bool IsAssignableFrom(Type c)
        {
            if (c == null) {
                return false;
            }

            // This excludes the TypeBuilder logic since Singularity does not
            // have TypeBuilder in our fork of the URT sources.

            // Check for interfaces
            if (IsInterface) {
                Type[] ifaces = c.GetInterfaces();
                for (int i=0;i<ifaces.Length;i++)
                    if (this == ifaces[i])
                        return true;
            }
            // Check the class relationship
            else {
                while (c != null) {
                    if (c == this)
                        return true;
                    c = c.BaseType;
                }
            }
            return false;
        }

        // ToString
        // Print the String Representation of the Type
        //| <include path='docs/doc[@for="Type.ToString"]/*' />
        public override String ToString()
        {
            return "Type: "+Name;
        }

        // This method will return an array of classes based upon the array of
        // types.
        //| <include path='docs/doc[@for="Type.GetTypeArray"]/*' />
        public static Type[] GetTypeArray(Object[] args)
        {
            if (args == null) {
                throw new ArgumentNullException("args");
            }
            Type[] cls = new Type[args.Length];
            for (int i = 0; i < cls.Length; i++) {
                cls[i] = args[i].GetType();
            }
            return cls;
        }

        //| <include path='docs/doc[@for="Type.Equals"]/*' />
        public override bool Equals(Object o)
        {
            if (o == null) {
                return false;
            }
            if (!(o is Type)) {
                return false;
            }
            return (this.UnderlyingSystemType == ((Type) o).UnderlyingSystemType);
        }

        //| <include path='docs/doc[@for="Type.Equals1"]/*' />
        public bool Equals(Type o)
        {
            if (o == null) {
                return false;
            }
            return (this.UnderlyingSystemType == o.UnderlyingSystemType);
        }

        //| <include path='docs/doc[@for="Type.GetHashCode"]/*' />
        public override int GetHashCode()
        {
            Type SystemType = UnderlyingSystemType;
            if (SystemType != this) {
                return SystemType.GetHashCode();
            }
            return base.GetHashCode();
        }

        // private convenience data
        private static readonly Type valueType = typeof(System.ValueType);
        private static readonly Type enumType = typeof(System.Enum);

        public abstract Microsoft.Singularity.V1.Types.SystemType GetSystemType();
    }
}

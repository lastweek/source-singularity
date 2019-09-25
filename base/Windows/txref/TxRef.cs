// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using System.Reflection;
using System.Collections;
using System.Text;

public class TypeWriter
{
    static Hashtable typeNames;
    static Hashtable opNames;
    static Hashtable opSortKeys;

    public static int memberCt;

    TextWriter writer;
    int indent;
    bool startOfLine;
    bool includeMemberKeys = false;
    bool fullTypeNames;

    public TypeWriter(TextWriter writer)
    {
        this.writer = writer;
    }

    static TypeWriter()
    {
        typeNames = new Hashtable();
        typeNames.Add(typeof(void), "void");
        typeNames.Add(typeof(System.Object), "object");
        typeNames.Add(typeof(System.String), "string");
        typeNames.Add(typeof(System.SByte), "sbyte");
        typeNames.Add(typeof(System.Byte), "byte");
        typeNames.Add(typeof(System.Int16), "short");
        typeNames.Add(typeof(System.UInt16), "ushort");
        typeNames.Add(typeof(System.Int32), "int");
        typeNames.Add(typeof(System.UInt32), "uint");
        typeNames.Add(typeof(System.Int64), "long");
        typeNames.Add(typeof(System.UInt64), "ulong");
        typeNames.Add(typeof(System.Char), "char");
        typeNames.Add(typeof(System.Boolean), "bool");
        typeNames.Add(typeof(System.Single), "float");
        typeNames.Add(typeof(System.Double), "double");
        typeNames.Add(typeof(System.Decimal), "decimal");
        opNames = new Hashtable();
        opNames.Add("op_UnaryPlus", "+");
        opNames.Add("op_Addition", "+");
        opNames.Add("op_Increment", "++");
        opNames.Add("op_UnaryNegation", "-");
        opNames.Add("op_Subtraction", "-");
        opNames.Add("op_Decrement", "--");
        opNames.Add("op_Multiply", "*");
        opNames.Add("op_Division", "/");
        opNames.Add("op_Modulus", "%");
        opNames.Add("op_BitwiseAnd", "&");
        opNames.Add("op_BitwiseOr", "|");
        opNames.Add("op_ExclusiveOr", "^");
        opNames.Add("op_Negation", "!");
        opNames.Add("op_OnesComplement", "~");
        opNames.Add("op_LeftShift", "<<");
        opNames.Add("op_RightShift", ">>");
        opNames.Add("op_Equality", "==");
        opNames.Add("op_Inequality", "!=");
        opNames.Add("op_GreaterThanOrEqual", ">=");
        opNames.Add("op_LessThanOrEqual", "<=");
        opNames.Add("op_GreaterThan", ">");
        opNames.Add("op_LessThan", "<");
        opNames.Add("op_True", "true");
        opNames.Add("op_False", "false");
        opNames.Add("op_Implicit", "implicit");
        opNames.Add("op_Explicit", "explicit");
        opSortKeys = new Hashtable();
        opSortKeys.Add("op_UnaryPlus", "A");
        opSortKeys.Add("op_Addition", "B");
        opSortKeys.Add("op_Increment", "C");
        opSortKeys.Add("op_UnaryNegation", "D");
        opSortKeys.Add("op_Subtraction", "E");
        opSortKeys.Add("op_Decrement", "F");
        opSortKeys.Add("op_Multiply", "G");
        opSortKeys.Add("op_Division", "H");
        opSortKeys.Add("op_Modulus", "I");
        opSortKeys.Add("op_BitwiseAnd", "J");
        opSortKeys.Add("op_BitwiseOr", "K");
        opSortKeys.Add("op_ExclusiveOr", "L");
        opSortKeys.Add("op_Negation", "M");
        opSortKeys.Add("op_OnesComplement", "N");
        opSortKeys.Add("op_LeftShift", "O");
        opSortKeys.Add("op_RightShift", "P");
        opSortKeys.Add("op_Equality", "Q");
        opSortKeys.Add("op_Inequality", "R");
        opSortKeys.Add("op_GreaterThanOrEqual", "S");
        opSortKeys.Add("op_LessThanOrEqual", "T");
        opSortKeys.Add("op_GreaterThan", "U");
        opSortKeys.Add("op_LessThan", "V");
        opSortKeys.Add("op_True", "W");
        opSortKeys.Add("op_False", "X");
        opSortKeys.Add("op_Implicit", "Y");
        opSortKeys.Add("op_Explicit", "Z");
    }

    public bool FullTypeNames
    {
        get { return fullTypeNames; }
        set { fullTypeNames = value; }
    }

    void AddMemberEntries(ArrayList list, Type type, bool inherited)
    {
        foreach (MemberInfo member in type.GetMembers(
            //| BindingFlags.DeclaredOnly
            BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static | BindingFlags.Public))
        {
            if (member.DeclaringType != member.ReflectedType) {
                continue;
            }
            // if (!inherited || member.MemberType != MemberTypes.Constructor) {
            list.Add(new MemberEntry(member));
            //}
        }
    }



    static void AppendParams(StringBuilder sb, ParameterInfo[] parameters)
    {
        sb.Append('(');
        for (int i = 0; i < parameters.Length; i++) {
            if (i != 0) sb.Append(',');
            AppendType(sb, parameters[i].ParameterType);
        }
        sb.Append(')');
    }

    static void AppendType(StringBuilder sb, Type type)
    {
        if (IsArray(type)) {
            AppendType(sb, type.GetElementType());
            sb.Append("[]");
        }
        else if (type.IsByRef) {
            AppendType(sb, type.GetElementType());
            sb.Append("@");
        }
        else if (type.IsPointer) {
            AppendType(sb, type.GetElementType());
            sb.Append("*");
        }
        else {
            sb.Append(type.FullName);
        }
    }



    static bool ContainsInterface(Type[] types, Type type)
    {
        foreach (Type t in types) {
            if (ContainsType(t.GetInterfaces(), type)) return true;
        }
        return false;
    }

    static bool ContainsType(Type[] types, Type type)
    {
        if (types != null) {
            foreach (Type t in types) {
                if (t == type) return true;
            }
        }
        return false;
    }

    static MethodInfo GetAccessor(EventInfo evnt)
    {
        return evnt.GetAddMethod();
    }

    static MethodInfo GetAccessor(PropertyInfo property)
    {
        MethodInfo result = property.GetGetMethod();
        if (result == null) result = property.GetSetMethod();
        return result;
    }

    static string GetMemberKey(MemberInfo member)
    {
        StringBuilder sb = new StringBuilder();
        switch (member.MemberType) {
            case MemberTypes.Constructor:
                sb.Append("M:");
                sb.Append(member.DeclaringType.FullName);
                sb.Append(".#ctor");
                AppendParams(sb, ((ConstructorInfo)member).GetParameters());
                break;
            case MemberTypes.Field:
                sb.Append("F:");
                sb.Append(member.DeclaringType.FullName);
                sb.Append('.');
                sb.Append(((FieldInfo)member).Name);
                break;
            case MemberTypes.Property:
                sb.Append("P:");
                sb.Append(member.DeclaringType.FullName);
                sb.Append('.');
                sb.Append(((PropertyInfo)member).Name);
                ParameterInfo[] pi = ((PropertyInfo)member).GetIndexParameters();
                if (pi.Length != 0) AppendParams(sb, pi);
                break;
            case MemberTypes.Method:
                sb.Append("M:");
                sb.Append(member.DeclaringType.FullName);
                sb.Append('.');
                sb.Append(((MethodInfo)member).Name);
                AppendParams(sb, ((MethodInfo)member).GetParameters());
                break;
            case MemberTypes.Event:
                sb.Append("E:");
                sb.Append(member.DeclaringType.FullName);
                sb.Append('.');
                sb.Append(((EventInfo)member).Name);
                break;
        }
        return sb.ToString().Trim();
    }

    string[] GetInterfaceNames(Type type)
    {
        Type[] typeIntfs = type.GetInterfaces();
        if (typeIntfs.Length == 0) return new string[0];
        Type[] baseIntfs = type.BaseType == null ? null : type.BaseType.GetInterfaces();
        ArrayList list = new ArrayList();
        foreach (Type intf in typeIntfs) {
            if (!ContainsInterface(typeIntfs, intf)) {
                string s = intf.Name;
#if GENERICS
                if (intf.HasGenericArguments) {
                    s+="<";
                    Type[] types = intf.GetGenericArguments();
                    for (int i = 0; i < types.Length; i++) {
                        if (i != 0) s+=", ";
                        s+=types[i].Name;
                    }
                    s+=">";
                }
#endif
                list.Add(s);
                s = "";
            }
        }
        list.Sort();
        return (string[])list.ToArray(typeof(string));
    }

    static bool IsVarArgs(MethodBase m)
    {
        return (m.CallingConvention == CallingConventions.VarArgs);
    }
    static bool IsArray(Type type)
    {
        return type.IsArray && type != typeof(Array);
    }

    static bool IsDelegate(Type type)
    {
        return type.IsSubclassOf(typeof(Delegate)) && type != typeof(MulticastDelegate);
    }

    static bool IsOverride(MethodInfo method)
    {
        return (method.Attributes & (MethodAttributes.Virtual |
            MethodAttributes.NewSlot)) == MethodAttributes.Virtual;
    }

    void Write(string s)
    {
        WriteIndent();
        writer.Write(s);
    }

    void Write(char ch)
    {
        WriteIndent();
        writer.Write(ch);
    }
    public void WriteNamespace(string namespaceName, Type[] types)
    {
        Write("namespace ");
        Write(namespaceName);
        WriteLine();
        Write("{");
        WriteLine();
        indent++;
        foreach (Type t in types) {
            if (t.IsPublic && t.Namespace == namespaceName) {
                WriteTypeDecl(t);
            }
        }
        indent--;
        Write("} ");
        WriteLine();
    }

    void WriteConstructor(ConstructorInfo ctor)
    {
        if (!(ctor.IsPublic || ctor.IsFamily || ctor.IsFamilyOrAssembly)) return;
        if (ctor.IsStatic) return;
        Write(ctor.IsPublic ? "public " : "protected ");
        Write(ctor.DeclaringType.Name);
        Write('(');
        WriteParamList(ctor.GetParameters());
        if (IsVarArgs(ctor)) {
            Write(", __arglist");
        }
        Write(");");
        WriteMemberEnd(ctor);
    }

    void WriteEvent(EventInfo evnt)
    {
        if (evnt.GetAddMethod() == null) {
            return;
        }
        if (!(evnt.GetAddMethod().IsPublic || evnt.GetAddMethod().IsFamily || evnt.GetAddMethod().IsFamilyOrAssembly)) return;
        memberCt++;
        Write(evnt.GetAddMethod().IsPublic ? "public " : "protected ");
        Write("event ");
        Write(evnt.EventHandlerType.Name);
        Write(" ");
        Write(evnt.Name);
        Write(";");
        WriteMemberEnd(evnt);
    }

    void WriteField(FieldInfo field)
    {
        if (!(field.IsPublic || field.IsFamily || field.IsFamilyOrAssembly)) return;
        if (field.DeclaringType.IsEnum) {
            if (!field.IsLiteral) return;
            Write(field.Name);
            Write(',');
        }
        else {
            Write(field.IsPublic ? "public " : "protected ");
            if (field.IsStatic && field.IsLiteral) {
                Write("const ");
            }
            else {
                if (field.IsStatic) Write("static ");
                if (field.IsInitOnly) Write("readonly ");
            }
            WriteType(field.FieldType);
            Write(' ');
            Write(field.Name);
            Write(';');
        }
        WriteMemberEnd(field);
    }

    void WriteIndent()
    {
        if (startOfLine) {
            for (int i = 0; i < indent; i++) writer.Write("    ");
            startOfLine = false;
        }
    }

    void WriteLine()
    {
        writer.WriteLine();
        startOfLine = true;
    }

    public void WriteMember(MemberInfo member)
    {
        switch (member.MemberType) {
            case MemberTypes.Constructor:
                WriteConstructor((ConstructorInfo)member);
                break;
            case MemberTypes.Field:
                WriteField((FieldInfo)member);
                break;
            case MemberTypes.Property:
                WriteProperty((PropertyInfo)member);
                break;
            case MemberTypes.Method:
                WriteMethod((MethodInfo)member);
                break;
            case MemberTypes.Event:
                WriteEvent((EventInfo)member);
                break;
        }
    }

    void WriteMemberEnd(MemberInfo member)
    {
        if (includeMemberKeys) {
            Write(" // ");
            Write(GetMemberKey(member));
        }
        WriteLine();
    }

    void WriteMethod(MethodInfo method)
    {
        if (!(method.IsPublic || method.IsFamily || method.IsFamilyOrAssembly)) return;
        if (method.IsSpecialName && !opNames.Contains(method.Name)) return;
        if (IsOverride(method)) Write(""); //return;
        memberCt++;
        Write(method.IsPublic ? "public " : "protected ");
        if (method.IsStatic) Write("static ");
        WriteMethodModifiers(method);
        if (method.IsSpecialName) {
            string op = (string)opNames[method.Name];
            if (op == "explicit" || op == "implicit") {
                Write(op);
                Write(" operator ");
                WriteType(method.ReturnType);
            }
            else {
                WriteType(method.ReturnType);
                Write(" operator ");
                Write(op);
            }
        }
        else {
            WriteType(method.ReturnType);
            Write(' ');
            Write(method.Name);
        }
#if GENERICS
        if (method.IsGenericMethodDefinition) {
            Write("<");
            WriteTypeList(method.GetGenericArguments());
            Write(">");
        }
#endif
        Write('(');
        WriteParamList(method.GetParameters());
        if (IsVarArgs(method)) {
            Write(", __arglist");
        }
        Write(");");
        WriteMemberEnd(method);
    }

    void WriteMethodModifiers(MethodInfo method)
    {
        if (method.DeclaringType.IsInterface) {
            return;
        }
        MethodAttributes attrs = method.Attributes;
        if ((attrs & MethodAttributes.Final) != 0 &&
            (attrs & MethodAttributes.Virtual) != 0 &&
            (attrs & MethodAttributes.NewSlot) != 0)
        {
            attrs = 0;
        }
        if ((attrs & MethodAttributes.Final) != 0) Write("sealed ");
        if ((attrs & MethodAttributes.Virtual) != 0) {
            switch (attrs & (MethodAttributes.NewSlot | MethodAttributes.Abstract)) {
                case 0:
                    Write("override ");
                    break;
                case MethodAttributes.NewSlot:
                    Write("virtual ");
                    break;
                case MethodAttributes.Abstract:
                    Write("abstract override ");
                    break;
                case MethodAttributes.NewSlot | MethodAttributes.Abstract:
                    Write("abstract ");
                    break;
            }
        }
    }

    void WriteParamList(ParameterInfo[] parameters)
    {
        for (int i = 0; i < parameters.Length; i++) {
            ParameterInfo param = parameters[i];
            if (i != 0) Write(", ");
            Type type = param.ParameterType;
            if (IsArray(type) && Attribute.IsDefined(param, typeof(ParamArrayAttribute), true)) {
                Write("params ");
            }
            WriteType(type);
            Write(' ');
            Write(param.Name);
        }
    }

    void WriteProperty(PropertyInfo property)
    {
        MethodInfo accessor = GetAccessor(property);
        if (accessor == null) return;
        if (!(accessor.IsPublic || accessor.IsFamily || accessor.IsFamilyOrAssembly)) return;
        if (IsOverride(accessor)) return;
        ParameterInfo[] parameters = property.GetIndexParameters();
        memberCt++;
        Write(accessor.IsPublic ? "public " : "protected ");
        if (accessor.IsStatic) Write("static ");
        WriteMethodModifiers(accessor);
        WriteType(property.PropertyType);
        Write(' ');
        if (parameters.Length == 0) {
            Write(property.Name);
        }
        else {
            Write("this[");
            WriteParamList(accessor.GetParameters());
            Write("]");
        }
        Write(" { ");
        if (property.CanRead) Write("get; ");
        if (property.CanWrite) Write("set; ");
        Write("}");
        WriteMemberEnd(property);
    }

    void WriteType(Type type)
    {

        if (IsArray(type)) {
            WriteType(type.GetElementType());
            Write('[');
            for (int i = type.GetArrayRank(); i > 1; i--) Write(',');
            Write(']');
        }
        else if (type.IsByRef) {
            Write("ref ");
            WriteType(type.GetElementType());
        }
        else if (type.IsPointer) {
            WriteType(type.GetElementType());
            Write('*');
        }
#if GENERICS
        else if (type.HasGenericArguments) {
            WriteSimpleTypeName(type);
            Write("<");
            WriteTypeList(type.GetGenericArguments());
            Write(">");
        }
#endif
        else {
            WriteSimpleTypeName(type);
        }
    }
    private void WriteTypeList(Type[] types)
    {
        for (int i = 0; i < types.Length; i++) {
            if (i != 0) Write(",");
            WriteType(types[i]);
        }
    }
    private void WriteSimpleTypeName(Type type)
    {
        string name = (string)typeNames[type];
        if (name == null) name = type.Name;
        Write(name);
    }

    public void WriteCustomAttribute(Attribute att)
    {
        Write("[");
        Write(att.GetType().Name);
        Write("(..)");
        Write("]");
        WriteLine();

    }

    public void WriteTypeDecl(Type type)
    {

        Attribute[] attrs = Attribute.GetCustomAttributes(type);
        foreach (Attribute a in attrs) {
            WriteCustomAttribute(a);
        }

        if (type.IsPublic || type.IsNestedPublic) {
            Write("public ");
        }
        else if (type.IsNestedPrivate) {
            Write("private ");
        }
        else if (type.IsNestedAssembly) {
            Write("internal ");
        }
        else if (type.IsNestedFamily) {
            Write("protected ");
        }
        else if (type.IsNestedFamORAssem) {
            Write("protected internal ");
        }
        if (IsDelegate(type)) {
            Write("delegate ");
            MethodInfo method = type.GetMethod("Invoke");
            WriteType(method.ReturnType);
            Write(' ');
            WriteTypeName(type);
            Write('(');
            WriteParamList(method.GetParameters());
            Write(")");
            WriteTypeConstraints(type);
            Write(";");
        }
        else {
            ArrayList list = new ArrayList();
            AddMemberEntries(list, type, true);
            if (type.IsEnum) {
                Write("enum ");
                WriteTypeName(type);
            }
            else {
                bool colonWritten = false;
                if (type.IsValueType) {
                    Write("struct ");
                    WriteTypeName(type);
                }
                else if (type.IsInterface) {
                    Write("interface ");
                    WriteTypeName(type);
                }
                else {
                    if (type.IsAbstract) Write("abstract ");
                    if (type.IsSealed) Write("sealed ");
                    Write("class ");
                    WriteTypeName(type);
                    Type baseType = type.BaseType;
                    if (baseType != null && baseType != typeof(object)) {
                        Write(": ");
                        Write(baseType.Name);
                        colonWritten = true;
                    }
                }
                foreach (string s in GetInterfaceNames(type)) {
                    Write(colonWritten ? ", " : ": ");
                    Write(s);
                    colonWritten = true;
                }
            }
            WriteTypeConstraints(type);
            WriteLine();
            Write('{');
            WriteLine();
            list.Sort();
            indent++;
            foreach (MemberEntry entry in list) {
                if (!entry.IsSecured)
                    WriteMember(entry.Member);
            }
            indent--;
            Write('}');
        }
        WriteLine();
        WriteLine();
    }

    void WriteTypeName(Type type)
    {

        Write(fullTypeNames ? type.FullName : type.Name);
#if GENERICS
        if (type.IsGenericTypeDefinition) {
            Write("<");
            WriteTypeList(type.GetGenericArguments());
            Write(">");
        }
#endif
    }
    void WriteTypeConstraints(Type type)
    {

#if GENERICS
        foreach (Type t in type.GetGenericArguments()) {
            Type[] arr = t.GetInterfaces();

            object[] arr2 = t.GetCustomAttributes(true);
            if (t.BaseType != typeof(object) || arr.Length + arr2.Length > 0) {
                Write(" where ");
                WriteTypeName(t);
                Write(":");
            }
            if (t.BaseType != typeof(Object)) {
                WriteTypeName(t.BaseType);
                if (arr.Length + arr2.Length > 0) Write(",");
            }
            for (int i = 0; i < arr.Length; i++) {
                WriteTypeName(arr[i]);
                if (i < arr.Length-1 || arr2.Length>0) Write(",");
            }

            for (int i = 0; i < arr2.Length; i++) {
                if (arr2[i].GetType() == typeof(System.Runtime.CompilerServices.NewConstraintAttribute)) {
                    Write("new()");
                }
                else {
                    Write(arr2[i].ToString());
                }
                if (i < arr.Length - 1) Write(",");
            }
        }
#endif
    }

    class MemberEntry : IComparable
    {
        MemberInfo member;
        string sortKey;
        bool secured = false;

        public MemberEntry(MemberInfo member)
        {
            this.member = member;
            try {
                StringBuilder sb = new StringBuilder();
                switch (member.MemberType) {
                    case MemberTypes.Constructor:
                        sb.Append('A');
                        AppendParams(sb, ((ConstructorInfo)member).GetParameters());
                        break;
                    case MemberTypes.Field:
                        sb.Append('B');
                        sb.Append(member.Name);
                        break;
                    case MemberTypes.Property:
                        ParameterInfo[] parameters = ((PropertyInfo)member).GetIndexParameters();
                        if (parameters.Length == 0) {
                            sb.Append('C');
                            sb.Append(member.Name);
                        }
                        else {
                            sb.Append('D');
                            AppendParams(sb, parameters);
                        }
                        break;
                    case MemberTypes.Method:
                        if (((MethodInfo)member).IsSpecialName && opSortKeys.Contains(member.Name)) {
                            sb.Append('F');
                            sb.Append((string)opSortKeys[member.Name]);
                            if (member.Name == "op_Implicit" || member.Name == "op_Explicit") {
                                AppendType(sb, ((MethodInfo)member).ReturnType);
                            }
                        }
                        else {
                            sb.Append('E');
                            sb.Append(member.Name);
                        }
                        AppendParams(sb, ((MethodInfo)member).GetParameters());
                        break;
                    case MemberTypes.Event:
                        sb.Append('G');
                        sb.Append(member.Name);
                        ((EventInfo)member).GetAddMethod(); // Force strong name security exception here
                        break;
                }
                sortKey = sb.ToString();
            }
            catch (System.Security.SecurityException) {
                secured = true;
            }

        }

        public MemberInfo Member
        {
            get { return member; }
        }

        public bool IsSecured
        {
            get { return secured; }
        }

        int IComparable.CompareTo(object other)
        {
            if (sortKey == null)
                return -1;
            return sortKey.CompareTo(((MemberEntry)other).sortKey);
        }

        static void AppendParams(StringBuilder sb, ParameterInfo[] parameters)
        {
            foreach (ParameterInfo param in parameters) {
                AppendType(sb, param.ParameterType);
            }
        }

        static void AppendType(StringBuilder sb, Type type)
        {
            if (IsArray(type)) {
                AppendType(sb, type.GetElementType());
                sb.Append("[]");
            }
            else if (type.IsByRef) {
                AppendType(sb, type.GetElementType());
                sb.Append("@");
            }
            else if (type.IsPointer) {
                AppendType(sb, type.GetElementType());
                sb.Append("*");
            }
            else {
                sb.Append(',');
                string name = (string)typeNames[type];
                if (name == null) name = type.Name;
                sb.Append(name);
            }
        }
    }
}

class TXRef
{
    static void Main(string[] args)
    {
#if GENERICS
        System.Diagnostics.Process.GetCurrentProcess().PriorityClass = System.Diagnostics.ProcessPriorityClass.Idle;
#endif

        TypeWriter writer = new TypeWriter(Console.Out);
        foreach (string s in args) {
            Assembly a = null;
            try {
                a = Assembly.LoadFrom(s);
                if (a == null)
                    a = Assembly.Load(s);
            }
            catch (Exception e) {
                Console.WriteLine(e);
            }
            if (a == null) {
                Console.WriteLine("TxRef: could not load assembly '{0}'.", s);
                return;
            }
            ArrayList l = new ArrayList();
            Type[] types;
            try {
                types = a.GetTypes();
            }
            catch (ReflectionTypeLoadException re) {
                foreach (Exception e in re.LoaderExceptions) {
                    Console.WriteLine(e);
                }
                types = RemoveNulls(re.Types);

            }

            Array.Sort(types, new TypeComparer());

            foreach (Type t in types) {
                if (t.IsPublic) {
                    if (!l.Contains(t.Namespace))
                        l.Add(t.Namespace);
                }
            }

            l.Sort(null);

            foreach (string namespaceName in l) {
                writer.WriteNamespace(namespaceName, types);
            }
        }
    }

    static Type[] RemoveNulls(Type[] types)
    {
        ArrayList l = new ArrayList();
        foreach (Type t in types) {
            if (t != null) l.Add(t);
        }
        return (Type[])l.ToArray(typeof(Type));
    }
}

public class TypeComparer : IComparer
{
    internal enum TypeGroup {
        MainGroup = 0,
        Enums = 1,
        Collections = 2,
        DelegatesAndEventArgs = 3,
        Attributes = 4,
        Exceptions = 5
    }

    internal static TypeGroup GetGroupForType(Type type) {
        if (type.IsEnum) return TypeGroup.Enums;
        if ((typeof(IEnumerable).IsAssignableFrom(type))) return TypeGroup.Collections;
        if (type.IsSubclassOf(typeof(Delegate)) || type.IsSubclassOf(typeof(EventArgs))) return TypeGroup.DelegatesAndEventArgs;
        if (type.IsSubclassOf(typeof(Attribute))) return TypeGroup.Attributes;
        if (type.IsSubclassOf(typeof(Exception))) return TypeGroup.Exceptions;
        return TypeGroup.MainGroup;
    }

    public int Compare(object obj1, object obj2)
    {
        Type t1 = obj1 as Type;
        Type t2 = obj2 as Type;

        // these are used to group by (for example all enums together)
        TypeGroup t1Group = TypeComparer.GetGroupForType(t1);
        TypeGroup t2Group = TypeComparer.GetGroupForType(t2);

        if (t2Group != t1Group) return ((int)t1Group) < ((int)t2Group) ? -1 : 1;
        return t1.Name.CompareTo(t2.Name);
    }
}

using System;
using System.IO;
using System.Collections;
using Bartok.MSIL;

using FieldAttributes = Bartok.MSIL.MetaDataField.FieldAttributes;
using MethodAttributes = Bartok.MSIL.MetaDataMethod.MethodAttributes;
using TypeAttributes = System.Reflection.TypeAttributes;

public class BartokReader: IImportReader {
    NameSpace global;
    MessageWriter msg;
    ArrayList metaData = new ArrayList();
    stringList loaded = new stringList();

    public BartokReader() {}
    public bool Load(string path) {
        if (path.StartsWith("./") || path.StartsWith(".\\"))
            path = path.Substring(2);
        if (!loaded.Contains(path))
            try {
                PELoader pe = new PELoader(path);
                long time = Debug.Clock;
                metaData.Add(MetaData.loadMetaData(path, pe, false, false));
                // Debug.Report("inhaling " + path, Debug.Clock - time);
                loaded.Add(path);
            } catch {
                return false;
            }
        // Add top-level namespaces to global namespace
        foreach (MetaData m in metaData)
            foreach (MetaDataTypeDefinition d in m.TypeDefs)
                if (d.Namespace != "")
                    GetNameSpace(d.Namespace);
        return true;
    }
    public Symbol Import(string fullname) {
        foreach (MetaData m in metaData)
            foreach (MetaDataTypeDefinition d in m.TypeDefs)
                if (d.FullName == fullname)
                    return GetSymbol(d, m.Name);
        return null;
    }
    public void Init(NameSpace global, MessageWriter msg) {
        this.global = global;
        this.msg = msg;
    }
    public SymbolList Lookup(string name, stringList namespaces) {
        SymbolList symbols = new SymbolList();
        foreach (MetaData m in metaData)
            foreach (MetaDataTypeDefinition d in m.TypeDefs)
                if (name == d.Name && (d.Namespace == "" || namespaces.Contains(d.Namespace)))
                    symbols.Add(GetSymbol(d, m.Name));
        return symbols;
    }

    NameSpace GetNameSpace(string ns) {
        NameSpace t = global;
        SymbolTable bindings = t.members;
        foreach (string name in ns.Split('.')) {
            t = bindings[name] as NameSpace;
            if (t == null) {
                t = new NameSpace(name, bindings);
                bindings.Add(name, t);
            }
            bindings = t.members;
        }
        return t;
    }
    Symbol GetSymbol(MetaDataTypeReference r) {
        if (r.ResolutionScope is MetaDataAssemblyRef) {
            string name = ((MetaDataAssemblyRef)r.ResolutionScope).Name;
            if (!Path.HasExtension(name))
                name += ".dll";
            Load(name);
        }
        if (r.Namespace == "") {
            if (r.ResolutionScope is MetaDataTypeReference
            && ((MetaDataTypeReference)r.ResolutionScope).Namespace != "")
                return Import(((MetaDataTypeReference)r.ResolutionScope).FullName + "." + r.Name);
            else
                return Import(r.Name);
        }
        Symbol s = Import(r.Namespace + "." + r.Name);
        if (s == null) {
            msg.Error("type or namespace '{0}' cannot be found\n" +
                "\t(missing using directive or assembly reference?)", r.FullName);
            return global.Types.Object;
        }
        return s;
    }
    Symbol GetSymbol(MetaDataTypeDefinition d, string path) {
        SymbolTable bindings;
        if (d.IsNestedType)
            bindings = ((ClassType)ResolveTypeRef(d.EnclosingClass, path)).members;
        else
            bindings = GetNameSpace(d.Namespace).members;
        Type t = bindings[d.Name] as Type;
        if (t != null)
            return t;
        switch ((int)d.Flags&(int)TypeAttributes.ClassSemanticsMask) {
        case (int)TypeAttributes.Class:
            switch (GetBaseClassName(d.Extends)) {
            case "System.Enum": t = GetEnum(d, bindings, path); break;
            case "System.Delegate":
            case "System.MulticastDelegate": t = GetDelegate(d, bindings, path); break;
            case "System.ValueType": t = GetStruct(d, bindings, path); break;
            default: t = GetClass(d, bindings, path); break;
            }
            break;
        case (int)TypeAttributes.Interface:
            t = GetInterface(d, bindings, path);
            break;
        default: Debug.Fail("unknown metadata type"); break;
        }
        t.module = path.ToLower();
        return t;
    }
    string GetBaseClassName(MetaDataObject d) {
        if (d is MetaDataTypeDefinition)
            return ((MetaDataTypeDefinition)d).FullName;
        else if (d is MetaDataTypeReference)
            return ((MetaDataTypeReference)d).Namespace + "." + ((MetaDataTypeReference)d).Name;
        return null;
    }
    Type ResolveTypeRef(MetaDataObject d, string path) {
        if (d is MetaDataTypeDefinition)
            return (Type)GetSymbol((MetaDataTypeDefinition)d, path);
        else if (d is MetaDataTypeReference)
            return (Type)GetSymbol((MetaDataTypeReference)d);
        else
            return null;
    }
    ClassType FillIn(ClassType t, MetaDataTypeDefinition d, string path) {
        foreach (MetaDataTypeDefinition x in d.NestedClasses)
            GetSymbol(x, path);
        foreach (MetaDataField x in d.Fields) {
            Field f = t.AddField(new InputElement(x.Name), msg);
            f.Modifiers = GetFieldModifiers(x);
            f.Type = GetType(x.Signature.FieldType, path);
        }
        foreach (MetaDataMethod x in d.Methods) {
            if (x.Name == "get_Item" || x.Name == "set_Item"
            || d.FullName == "System.String" && x.Name == "get_Chars")
                GetMethod(t, x.Name, x, path);  // indexer
            else if (x.Name.StartsWith("get_") || x.Name.StartsWith("set_")) {
                Property p;
                string name = x.Name.Substring(4);
                if (t.members.Contains(name))
                    p = (Property)t.members[name];
                else
                    p = t.AddProperty(new InputElement(name), msg);
                p.Modifiers = GetMethodModifiers(x);
                Method m;
                if (x.Name.StartsWith("get_")) {
                    m = p.AddGet(new InputElement(name));
                    m.Type = GetType(x.Signature.ReturnType, path);
                } else {
                    m = p.AddSet(new InputElement(name));
                    p.Type = GetType(x.Signature.Parameters[0].Type, path);
                    m.Type = global.Types.Void;
                }
                m.Modifiers = p.Modifiers;
            } else if (x.Name == ".ctor")
                GetMethod(t.AddConstructor(new InputElement(t.Name), msg), x, path);
            else if (x.Name == ".cctor") {
                Constructor m = new Constructor(new InputElement(t.Name), t.members);
                GetMethod(m, x, path);
            } else
                GetMethod(t, x.Name, x, path);
        }
        t.Modifiers = GetTypeModifiers(d);
        t.baseClass = (ClassType)ResolveTypeRef(d.Extends, path);
        t.enclosingType = (ClassType)ResolveTypeRef(d.EnclosingClass, path);
        foreach (MetaDataObject x in d.Interfaces) {
            InterfaceType f = ResolveTypeRef(x, path) as InterfaceType;
            if (f != null)
                t.interfaces.Add(f);
        }
        return t;
    }
    Method GetMethod(Method m, MetaDataMethod x, string path) {
        m.Modifiers = GetMethodModifiers(x);
        m.Type = GetType(x.Signature.ReturnType, path);
        for (int i = 0; i < x.Parameters.Length; i++) {
            Formal f;
            MetaDataParam p = x.Parameters[i];
            if (i == x.Parameters.Length - 1 && m.Name == "set_Item") {
                f = m.AddFormal(new InputElement("value"), msg);
                m.signature.formals.Remove(f);
            } else
                f = m.AddFormal(new InputElement(String.Format("arg{0}", i+1)), msg);
            f.Type = GetType(x.Signature.Parameters[i].Type, path);
            if ((p.Flags&((int)MetaDataParam.ParamAttributes.Out)) != 0)
                f.modifier = new InputElement("out");
            else if (f.Type is ManagedPointerType)
                f.modifier = new InputElement("ref");
            if (f.Type is ManagedPointerType)
                f.Type = ((ManagedPointerType)f.Type).elementType;
            else if (p.CustomAttributes != null)
                foreach (MetaDataCustomAttribute a in p.CustomAttributes) {
                    MetaDataMethod t = a.Type as MetaDataMethod;
                    if (t != null && t.Parent != null && t.Parent.Name == "ParamArrayAttribute") {
                        f.IsParams = true;
                        break;
                    }
                }
        }
        return m;
    }
    Method GetMethod(ClassType t, string name, MetaDataMethod x, string path) {
        return GetMethod(t.AddMethod(new InputElement(name), msg), x, path);
    }
    ClassType GetClass(MetaDataTypeDefinition d, SymbolTable bindings, string path) {
        ClassType t = new ClassType(new InputElement(d.Name), bindings);
        bindings.Add(t.Name, t);
        return FillIn(t, d, path);
    }
    StructType GetStruct(MetaDataTypeDefinition d, SymbolTable bindings, string path) {
        StructType t = new StructType(new InputElement(d.Name), bindings);
        bindings.Add(t.Name, t);
        return (StructType)FillIn(t, d, path);
    }
    InterfaceType GetInterface(MetaDataTypeDefinition d, SymbolTable bindings, string path) {
        InterfaceType t = new InterfaceType(new InputElement(d.Name), bindings);
        bindings.Add(t.Name, t);
        return (InterfaceType)FillIn(t, d, path);
    }
    EnumType GetEnum(MetaDataTypeDefinition d, SymbolTable bindings, string path) {
        EnumType t = new EnumType(new InputElement(d.Name), bindings);
        bindings.Add(t.Name, t);
        MetaDataField v = null;
        foreach (MetaDataField x in d.Fields)
            if (x.Name == "value__") {
                v = x;
                break;
            }
        t.baseType = GetType(v.Signature.FieldType, path);
        foreach (MetaDataField x in d.Fields)
            if (x != v) {
                EnumMember e = t.AddEnumMember(new InputElement(x.Name), msg);
                e.Type = t;
                e.value = x.DefaultValue;
            }
        t.Modifiers = GetTypeModifiers(d);
        return t;
    }
    DelegateType GetDelegate(MetaDataTypeDefinition d, SymbolTable bindings, string path) {
        DelegateType t = new DelegateType(new InputElement(d.Name), bindings);
        bindings.Add(t.Name, t);
        FillIn(t, d, path);
        MethodSuite m = t.members["Invoke"] as MethodSuite;
        if (m != null && m.Count == 1)
            t.invoke = m[0];
        return t;
    }
    Type GetType(Bartok.MSIL.Signature.Type type, string path) {
        if (type == null)
            return global.Types.TypedReference;
        switch (type.ElementType) {
        case ElementTypes.VOID: return global.Types.Void;
        case ElementTypes.BOOLEAN: return global.Types.Bool;
        case ElementTypes.CHAR: return global.Types.Char;
        case ElementTypes.I1: return global.Types.SByte;
        case ElementTypes.U1: return global.Types.Byte;
        case ElementTypes.I2: return global.Types.Short;
        case ElementTypes.U2: return global.Types.UShort;
        case ElementTypes.I:
        case ElementTypes.I4: return global.Types.Int;
        case ElementTypes.U:
        case ElementTypes.U4: return global.Types.UInt;
        case ElementTypes.I8: return global.Types.Long;
        case ElementTypes.U8: return global.Types.ULong;
        case ElementTypes.R4: return global.Types.Float;
        case ElementTypes.R8: return global.Types.Double;
        case ElementTypes.OBJECT: return global.Types.Object;
        case ElementTypes.STRING: return global.Types.String;
        case ElementTypes.TYPEDBYREF: return global.Types.TypedReference;
        case ElementTypes.VALUETYPE:
        case ElementTypes.CLASS:
            Type t = ResolveTypeRef(type.ClassObject, path);
            if (t == null)
                Debug.Fail("unknown CLASSTYPE " + type.ClassObject.ToStringLong());
            return t;
        case ElementTypes.SZARRAY:
            return new ArrayType(GetType(type.TypeObject, path), global.Types.Array);
        case ElementTypes.ARRAY:
            return new ArrayType(GetType(type.TypeObject, path), type.Rank, global.Types.Array);
        case ElementTypes.FNPTR:
        case ElementTypes.CMOD_OPT:
        case ElementTypes.CMOD_REQD: return GetType(type.TypeObject, path);
        case ElementTypes.PINNED:
        case ElementTypes.PTR:
            return new UnmanagedPointerType(GetType(type.TypeObject, path));
        case ElementTypes.BYREF:
            return new ManagedPointerType(GetType(type.TypeObject, path));
        default:
            Debug.Fail("unknown element type " + type); break;
        }
        return global.Types.Object;
    }
    stringList GetFieldModifiers(MetaDataField f) {
        stringList mods = new stringList();
        switch (f.Flags&(int)(FieldAttributes.FieldAccessMask)) {
        case (int)FieldAttributes.Private: mods.Add("private"); break;
        case (int)FieldAttributes.FamORAssem:
            mods.Add("protected"); mods.Add("internal"); break;
        case (int)FieldAttributes.Assembly: mods.Add("internal"); break;
        case (int)FieldAttributes.Family: mods.Add("protected"); break;
        case (int)FieldAttributes.Public: mods.Add("public"); break;
        }
        if ((f.Flags&(int)FieldAttributes.Static) != 0) mods.Add("static");
        return mods;
    }
    stringList GetMethodModifiers(MetaDataMethod m) {
        stringList mods = new stringList();
        switch (m.Flags&(int)(MethodAttributes.MemberAccessMask)) {
        case (int)MethodAttributes.Private: mods.Add("private"); break;
        case (int)MethodAttributes.FamORAssem:
            mods.Add("protected"); mods.Add("internal"); break;
        case (int)MethodAttributes.Assem:  mods.Add("internal"); break;
        case (int)MethodAttributes.Family: mods.Add("protected"); break;
        case (int)MethodAttributes.Public: mods.Add("public"); break;
        }
        if ((m.Flags&(int)MethodAttributes.Final)    != 0) mods.Add("sealed");
        if ((m.Flags&(int)MethodAttributes.Virtual)  != 0) mods.Add("virtual");
        if ((m.Flags&(int)MethodAttributes.Static)   != 0) mods.Add("static");
        if ((m.Flags&(int)MethodAttributes.Abstract) != 0) mods.Add("abstract");
        return mods;
    }
    stringList GetTypeModifiers(MetaDataTypeDefinition d) {
        stringList mods = new stringList();
        switch ((int)d.Flags&(int)(TypeAttributes.VisibilityMask)) {
        case (int)TypeAttributes.NotPublic: case (int)TypeAttributes.NestedPrivate:
            mods.Add("private"); break;
        case (int)TypeAttributes.NestedFamORAssem:
            mods.Add("protected"); mods.Add("internal"); break;
        case (int)TypeAttributes.NestedAssembly: mods.Add("internal"); break;
        case (int)TypeAttributes.NestedFamily:   mods.Add("protected"); break;
        case (int)TypeAttributes.Public: case (int)TypeAttributes.NestedPublic:
            mods.Add("public"); break;
        }
        if (((int)d.Flags&(int)TypeAttributes.Sealed)   != 0) mods.Add("sealed");
        if (((int)d.Flags&(int)TypeAttributes.Abstract) != 0) mods.Add("abstract");
        return mods;
    }
}

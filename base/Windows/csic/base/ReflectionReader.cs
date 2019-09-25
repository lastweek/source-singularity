using System;
using System.IO;
using System.Collections;
using System.Reflection;
using System.Reflection.Emit;

public class ReflectionReader: IImportReader {
	ArrayList assemblies = new ArrayList();
	NameSpace global;
	MessageWriter msg;

	public Symbol Import(string fullname) {
		System.Type type = System.Type.GetType(fullname, false);
		if (type != null)
			return GetSymbol(type);
		return null;
	}
	public void Init(NameSpace global, MessageWriter msg) {
		this.global = global;
		this.msg = msg;
	}
	public void Load(AssemblyBuilder asm) {
		ModuleBuilder module = asm.GetDynamicModule(asm.GetName().Name);
		long time = Debug.Clock;
		foreach (System.Type t in module.GetTypes())
			GetType(t);
		Debug.Report("inhaled " + asm.ToString(), Debug.Clock - time);
	}
	public void Load(Assembly asm) {
		if (!assemblies.Contains(asm)) {
			long time = Debug.Clock;
			foreach (System.Type t in asm.GetTypes())
				GetType(t);
			Debug.Report("inhaled " + asm.Location, Debug.Clock - time);
			assemblies.Add(asm);
		}
	}
	public bool Load(string path) {
		try {
			Assembly asm = Assembly.LoadFile(path);
			Load(asm);
		} catch (ArgumentException) {
			return false;
		} catch (FileNotFoundException) {
			return false;
		} catch (BadImageFormatException) {
			return false;
		} catch {
			throw;
		}
		return true;
	}
	public SymbolList Lookup(string name, stringList namespaces) {
		SymbolList symbols = new SymbolList();
		foreach (Assembly a in assemblies)
			foreach (System.Type t in a.GetTypes())
				if (name == GetName(t) && (t.Namespace == "" || t.Namespace == null || namespaces.Contains(t.Namespace)))
					symbols.Add(GetSymbol(t));
		return symbols;
	}
	public ReflectionReader() {}

	static BindingFlags flags = BindingFlags.Public|BindingFlags.NonPublic|BindingFlags.DeclaredOnly;
	ClassType FillIn(ClassType t, System.Type type) {
		foreach (System.Type x in type.GetNestedTypes(flags))
			GetType(x);
		foreach (FieldInfo x in type.GetFields(BindingFlags.Instance|BindingFlags.Static|flags)) {
			Field f = t.AddField(new InputElement(x.Name), msg);
			f.Modifiers = GetFieldModifiers(x);
			f.Type = GetType(x.FieldType);
		}
		foreach (ConstructorInfo x in type.GetConstructors(BindingFlags.Instance|BindingFlags.Static|flags))
			GetMethod(t.AddConstructor(new InputElement(t.Name), msg), x);
		foreach (MethodInfo x in type.GetMethods(BindingFlags.Instance|BindingFlags.Static|flags)) {
			if (x.Name == "get_Item" || x.Name == "set_Item"
			|| type.FullName == "System.String" && x.Name == "get_Chars")
				GetMethod(t, x.Name, x);	// indexer
			else if (x.Name.StartsWith("get_") || x.Name.StartsWith("set_")) {
				string name = x.Name.Substring(4);
				Property p = t.members[name] as Property;
				if (p == null)
					p = t.AddProperty(new InputElement(name), msg);
				p.Modifiers = GetMethodModifiers(x);
				Method m;
				if (x.Name.StartsWith("get_")) {
					m = p.AddGet(new InputElement(name));
					p.Type = GetType(x.ReturnType);
				} else {
					m = p.AddSet(new InputElement(name));
					m.Type = global.Types.Void;
					p.Type = GetType(x.GetParameters()[0].ParameterType);
				}
			} else
				GetMethod(t, x.Name, x);
		}
		t.Modifiers = GetTypeModifiers(type);
		IList baseinterfaces;
		if (type.BaseType != null) {
			t.baseClass = (ClassType)GetType(type.BaseType);
			baseinterfaces = type.BaseType.GetInterfaces();
		} else
			baseinterfaces = new System.Type[0];
		if (type.DeclaringType != null)
			t.enclosingType = (ClassType)GetType(type.DeclaringType);
		foreach (System.Type x in type.GetInterfaces())
			if (!baseinterfaces.Contains(x))
				t.interfaces.Add((InterfaceType)GetType(x));
		return t;
	}
	ClassType GetClass(System.Type type, SymbolTable bindings) {
		string name = GetName(type);
		ClassType t = new ClassType(new InputElement(name), bindings);
		bindings.Add(t.Name, t);
		return FillIn(t, type);
	}
	DelegateType GetDelegate(System.Type type, SymbolTable bindings) {
		string name = GetName(type);
		DelegateType t = new DelegateType(new InputElement(name), bindings);
		bindings.Add(t.Name, t);
		FillIn(t, type);
		MethodSuite m = t.members["Invoke"] as MethodSuite;
		if (m != null && m.Count == 1)
			t.invoke = m[0];
		return t;
	}
	EnumType GetEnum(System.Type type, SymbolTable bindings) {
		string name = GetName(type);
		EnumType t = new EnumType(new InputElement(name), bindings);
		bindings.Add(t.Name, t);
		t.baseType = GetType(Enum.GetUnderlyingType(type));
		string[] names = Enum.GetNames(type);
		Array values = Enum.GetValues(type);
		Debug.Assert(names.Length == values.Length);
		for (int i = 0; i < names.Length; i++) {
			EnumMember e = t.AddEnumMember(new InputElement(names[i]), msg);
			e.Type = t;
			object value = values.GetValue(i);
			if (!(value is int)) {
				FieldInfo f = value.GetType().GetField("value__");
				value = f.GetValue(value);
			}
			e.value = value;
		}
		t.Modifiers = GetTypeModifiers(type);
		return t;
	}
	stringList GetFieldModifiers(FieldInfo info) {
		stringList mods = new stringList();
		     if (info.IsPrivate) mods.Add("private");
		else if (info.IsFamilyOrAssembly) { mods.Add("protected"); mods.Add("internal"); }
		else if (info.IsAssembly) mods.Add("internal");
		else if (info.IsFamily) mods.Add("protected");
		else if (info.IsPublic) mods.Add("public");
		if (info.IsStatic) mods.Add("static");
		return mods;
	}
	InterfaceType GetInterface(System.Type type, SymbolTable bindings) {
		string name = GetName(type);
		InterfaceType t = new InterfaceType(new InputElement(name), bindings);
		bindings.Add(t.Name, t);
		return (InterfaceType)FillIn(t, type);
	}
	static System.Type paramArrayType = System.Type.GetType("System.ParamArrayAttribute");
	Method GetMethod(Method m, MethodBase info) {
		m.Modifiers = GetMethodModifiers(info);
		if (info is MethodInfo)
			m.Type = GetType(((MethodInfo)info).ReturnType);
		else
			m.Type = global.Types.Void;
		Formal f = null;
		foreach (ParameterInfo x in info.GetParameters()) {
			f = m.AddFormal(new InputElement(x.Name), msg);
			f.Type = GetType(x.ParameterType);
			if (x.IsOut)
				f.modifier = new InputElement("out");
			else if (f.Type is ManagedPointerType)
				f.modifier = new InputElement("ref");
			if (f.Type is ManagedPointerType)
				f.Type = ((ManagedPointerType)f.Type).elementType;
			else {
				object[] attrs = x.GetCustomAttributes(paramArrayType, false);
				if (attrs.Length > 0) {
					Debug.Assert(attrs.Length == 1);
					f.IsParams = true;
				}
			}
		}
		if (f != null && m.Name == "set_Item")
			m.signature.formals.Remove(f);
		return m;
	}
	Method GetMethod(ClassType t, string name, MethodBase info) {
		return GetMethod(t.AddMethod(new InputElement(name), msg), info);
	}
	stringList GetMethodModifiers(MethodBase info) {
		stringList mods = new stringList();
		     if (info.IsPrivate) mods.Add("private");
		else if (info.IsFamilyOrAssembly) { mods.Add("protected"); mods.Add("internal"); }
		else if (info.IsAssembly) mods.Add("internal");
		else if (info.IsFamily) mods.Add("protected");
		else if (info.IsPublic) mods.Add("public");
		if (info.IsFinal) mods.Add("sealed");
		if (info.IsVirtual) mods.Add("virtual");
		if (info.IsStatic) mods.Add("static");
		if (info.IsAbstract) mods.Add("abstract");
		return mods;
	}
	string GetName(System.Type type) {
		if (type.Namespace != null)
            return type.FullName.Substring(type.Namespace.Length + 1);
		else
			return type.FullName;
	}
	NameSpace GetNameSpace(System.Type type) {
		NameSpace t = global;
		SymbolTable bindings = t.members;
		if (type.Namespace != null)
			foreach (string name in type.Namespace.Split('.')) {
				t = bindings[name] as NameSpace;
				if (t == null) {
					t = new NameSpace(name, bindings);
					bindings.Add(name, t);
				}
				bindings = t.members;
			}
		return t;
	}
	StructType GetStruct(System.Type type, SymbolTable bindings) {
		string name = GetName(type);
		StructType t = new StructType(new InputElement(name), bindings);
		bindings.Add(t.Name, t);
		return (StructType)FillIn(t, type);
	}
	Symbol GetSymbol(System.Type type) {
		NameSpace ns = GetNameSpace(type);
		string name = GetName(type);
		Type t = ns.members[name] as Type;
		if (t != null)
			return t;
		if (type.IsInterface)
			t = GetInterface(type, ns.members);
		else if (type.IsEnum)
			t = GetEnum(type, ns.members);
		else if (type.IsValueType)
			t = GetStruct(type, ns.members);
		else if (type.IsClass
		&& (type.BaseType == typeof (System.Delegate) || type.BaseType == typeof (System.MulticastDelegate)))
			t = GetDelegate(type, ns.members);
		else if (type.IsArray)
			t = new ArrayType(GetType(type.GetElementType()), type.GetArrayRank(), global.Types.Array);
		else if (type.IsByRef)
			t = new ManagedPointerType(GetType(type.GetElementType()));
		else if (type.IsPointer)
			t = new UnmanagedPointerType(GetType(type.GetElementType()));
		else if (type.IsClass || type.IsAnsiClass)
			t = GetClass(type, ns.members);
		else
			Debug.Fail("unknown type " + type.FullName);
		t.module = type.Assembly.Location.ToLower();
		t.type = type;
		return t;
	}
	Type GetType(System.Type type) {
		Type ty;
		     if (type == typeof (void))   ty = global.Types.Void;
		else if (type == typeof (bool))   ty = global.Types.Bool;
		else if (type == typeof (char))   ty = global.Types.Char;
		else if (type == typeof (sbyte))  ty = global.Types.SByte;
		else if (type == typeof (byte))   ty = global.Types.Byte;
		else if (type == typeof (short))  ty = global.Types.Short;
		else if (type == typeof (ushort)) ty = global.Types.UShort;
		else if (type == typeof (int))    ty = global.Types.Int;
		else if (type == typeof (uint))   ty = global.Types.UInt;
		else if (type == typeof (long))   ty = global.Types.Long;
		else if (type == typeof (ulong))  ty = global.Types.ULong;
		else if (type == typeof (float))  ty = global.Types.Float;
		else if (type == typeof (double)) ty = global.Types.Double;
		else if (type == typeof (object)) ty = global.Types.Object;
		else if (type == typeof (string)) ty = global.Types.String;
		else ty = (Type)GetSymbol(type);
		ty.type = type;
		return ty;
	}
	stringList GetTypeModifiers(System.Type type) {
		stringList mods = new stringList();
		     if (type.IsNestedPrivate || type.IsNotPublic) mods.Add("private");
		else if (type.IsNestedFamORAssem) { mods.Add("protected"); mods.Add("internal"); }
		else if (type.IsNestedAssembly) mods.Add("internal");
		else if (type.IsNestedFamily) mods.Add("protected");
		else if (type.IsPublic || type.IsNestedPublic) mods.Add("public");
		if (type.IsSealed) mods.Add("sealed");
		if (type.IsAbstract) mods.Add("abstract");
		return mods;
	}
}

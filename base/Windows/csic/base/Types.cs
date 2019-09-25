using System;
using System.IO;
using System.Collections;
using System.Reflection;

public class ArrayType: Type {
	public int rank = 1;
	public Type elementType;
	ClassType baseType;	// System.Array
	public ArrayType(Type elementType, ClassType baseType) : this(elementType, 1, baseType) {
	}
	public ArrayType(Type elementType, int rank, ClassType baseType) {
		this.elementType = elementType;
		this.rank = rank;
		this.baseType = baseType;
	}
	override public bool Equals(Type t) {
		return t is ArrayType && rank == ((ArrayType)t).rank
			&& Equals(elementType, ((ArrayType)t).elementType);
	}
	public override string FullName {
		get { return string.Format("{0}[{1}]", elementType.FullName, "".PadRight(rank - 1, ',')); }
	}
	override public bool Implements(Type t) {
		return baseType.Implements(t);
	}
	override public bool InheritsFrom(Type t) {
		return baseType.InheritsFrom(t);
	}
	override public bool IsReferenceType {
		get { return true; }
	}
	override public Symbol Lookup(InputElement id, MessageWriter msg) {
		return baseType.Lookup(id, msg);
	}
	public override string Name {
		get { return string.Format("{0}[{1}]", elementType.Name, "".PadRight(rank - 1, ',')); }
	}
	public override string RealName {
		get { return string.Format("{0}[{1}]", elementType.RealName, "".PadRight(rank - 1, ',')); }
	}
	override public void Write(TextWriter w) {
		elementType.Write(w);
		w.Write("[{0}]", "".PadRight(rank - 1, ','));
	}
}

public class ClassType: Type, INamespaceOrType {
	class classEnumerator: IEnumerator {
		IEnumerator e;
		Symbol current = null;
		int i = 0;
		public classEnumerator(ClassType c) {
			e = c.members.GetEnumerator();
		}
		public Symbol Current {
			get {
				if (current == null)
					throw new InvalidOperationException("classEnumerator usage");
				if (current is MethodSuite)
					return ((MethodSuite)current)[i];
				return current;
			}
		}
		object IEnumerator.Current {
			get { return Current; }
		}
		public bool MoveNext() {
			if (current is MethodSuite && ++i < ((MethodSuite)current).methods.Count)
				return true;
			if (e.MoveNext()) {
				current = (Symbol)((DictionaryEntry)e.Current).Value;
				i = 0;
				return true;
			}
			return false;
		}
		public void Reset() {
			e.Reset();
			current = null;
		}
	}
	public ClassType baseClass;
	public InterfaceTypeList interfaces = new InterfaceTypeList();
	public SymbolTable members;
	public virtual Constant AddConstant(InputElement id, MessageWriter msg) {
		Constant t = new Constant(id, members);
		t.Add(id, msg);
		return t;
	}
	public virtual Constructor AddConstructor(InputElement id, MessageWriter msg) {
		MethodSuite t = members[id.str] as MethodSuite;
		if (t == null) {
			t = new MethodSuite(id, members);
			t.Add(id, msg);
		}
		return (Constructor)t.Add(new Constructor(id, members));
	}
	public virtual Event AddEvent(InputElement id, MessageWriter msg) {
		Event t = new Event(id, members);
		((Symbol)t).Add(id, msg);
		return t;
	}
	public virtual Field AddField(InputElement id, MessageWriter msg) {
		Field t = new Field(id, members);
		t.Add(id, msg);
		return t;
	}
	public virtual Method AddMethod(InputElement id, MessageWriter msg) {
		MethodSuite t = members[id.str] as MethodSuite;
		if (t == null) {
			t = new MethodSuite(id, members);
			t.Add(id, msg);
		}
		return t.Add(new Method(id, members));
	}
	public virtual Property AddProperty(InputElement id, MessageWriter msg) {
		Property t = new Property(id, members);
		t.Add(id, msg);
		return t;
	}
	public ClassType(InputElement id, SymbolTable declSpace) : base(id, declSpace) {
		members = new SymbolTable(this);
	}
	public virtual SymbolList Flatten() {
		SymbolList all = new SymbolList();
		foreach (Symbol s in this)
			all.Add(s);
		for (ClassType c = this.baseClass; c != null; c = c.baseClass)
			foreach (Symbol s in c) {
				if (s.Is("private"))
					continue;
				if (s is Method || s is Property || s is Event) {
					int i;
					for (i = 0; i < all.Count; i++)
						if (s.Equals(all[i]))
							  break;
					if (i == all.Count || s.Is("abstract") && !all[i].Is("override"))
						all.Add(s);
				} else
					all.Add(s);
			}
		return all;
	}
	public virtual Method FindMethod(string name, params Type[] args) {
		for (ClassType c = this; c != null; c = c.baseClass) {
			Method m;
			MethodSuite t = c.members[name] as MethodSuite;
			if (t != null && (m = t.FindMethod(args)) != null)
				return m;
		}
		return null;
	}
	override public IEnumerator GetEnumerator() {
		return new classEnumerator(this);
	}
	override public bool Implements(Type t) {
		if (t is InterfaceType)
			for (ClassType c = this; c != null; c = c.baseClass)
				if (c.interfaces.Contains((InterfaceType)t))
					return true;
		return false;
	}
	override public bool InheritsFrom(Type t) {
		ClassType c = this;
		for ( ; c != null && c != t; c = c.baseClass)
			;
		return c == t;
	}
	override public bool IsClass {
		get { return true; }
	}
	override public bool IsReferenceType {
		get { return true; }
	}
	override public Symbol Lookup(InputElement id, MessageWriter msg) {
		MethodSuite methods = null;
		for (ClassType c = this; c != null; c = c.baseClass) {
			if (methods == null && id.str == c.id.str)
				return c;
			Symbol t = c.members[id.str];
			if (t != null && t.Is("override"))
				t = null;
			if (t != null && t is MethodSuite) {
				if (methods == null)
					methods = new MethodSuite(t.id);
				// add methods in t to methods
				foreach (Method m in ((MethodSuite)t).methods)
					if (methods.Contains(m.signature) == null)
						methods.Add(m);
			} else if (t != null && methods == null)
				return t;
		}
		if (methods != null)
			return methods;
		return declSpace.Owner.Lookup(id, msg);
	}
	override public Symbol LookupType(InputElement id, MessageWriter msg) {
		Symbol t = this[id.str];
		if (t is INamespaceOrType)
			return t;
		return declSpace.Owner.Lookup(id, msg);
	}
	public Symbol this[string id] {
		get {
			for (ClassType c = this; c != null; c = c.baseClass) {
				Symbol t = c.members[id];
				if (t is INamespaceOrType)
					return t;
			}
			return null;
		}
	}
}

public class DelegateType: ClassType {
	public Method invoke;
	public Formal AddFormal(InputElement id, MessageWriter msg) {
		return invoke.AddFormal(id, msg);
	}
	public DelegateType(InputElement id, SymbolTable declSpace) : base(id, declSpace) {
	}
	override public bool Equals(Type t) {
		DelegateType d = t as DelegateType;
		return d != null && invoke.Type.Equals(d.invoke.Type)
			&& invoke.signature.Equals(d.invoke.signature);
	}
	override public bool Implements(Type t) {
		return false;
	}
	override public bool IsClass {
		get { return false; }
	}
	override public Type Type {
		get { return invoke.Type; }
		set { invoke.Type = value; }
	}
}

public class EnumType: Type, INamespaceOrType {
	public Type baseType;
	public SymbolTable members;
	public EnumMember AddEnumMember(InputElement id, MessageWriter msg) {
		EnumMember t = new EnumMember(id, members);
		t.Add(id, msg);
		return t;
	}
	public EnumType(InputElement id, SymbolTable declSpace) : base(id, declSpace) {
		members = new SymbolTable(this);
	}
	override public bool IsValueType {
		get { return true; }
	}
	override public Symbol Lookup(InputElement id, MessageWriter msg) {
		Symbol t = this[id.str];
		if (t != null)
			return t;
		return declSpace.Owner.Lookup(id, msg);
	}
	public Symbol this[string id] {
		get { return members[id]; }
	}
}

public class InterfaceType: ClassType {
	public InterfaceType(InputElement id, SymbolTable declSpace) : base(id, declSpace) {}
	override public bool IsClass {
		get { return false; }
	}
	override public bool IsReferenceType {
		get { return true; }
	}
	override public Symbol Lookup(InputElement id, MessageWriter msg) {
		MethodSuite methods = null;
		int i = 0;
		for (InterfaceType c = this; c != null; c = i < interfaces.Count ? interfaces[i++] : null) {
			Symbol t = c.members[id.str];
			if (t != null && t is MethodSuite) {
				if (methods == null)
					methods = new MethodSuite(t.id);
				// add methods in t to methods
				foreach (Method m in ((MethodSuite)t).methods)
						if (methods.Contains(m.signature) == null)
					methods.Add(m);
			} else if (t != null && methods == null)
				return t;
		}
		if (methods != null)
			return methods;
		return declSpace.Owner.Lookup(id, msg);
	}
}

public class ManagedPointerType: PointerType {
	override public bool Equals(Type t) {
		return t is ManagedPointerType && elementType.Equals(((ManagedPointerType)t).elementType);
	}
	public override string Name {
		get { return elementType.Name + "&"; }
	}
	public override string RealName {
		get { return elementType.RealName + "&"; }
	}
	public ManagedPointerType(Type elementType) : base(elementType) { }
	override public void Write(TextWriter w) {
		elementType.Write(w);
		w.Write("&");
	}
}

abstract public class PointerType: Type {
	public Type elementType;
	public PointerType(Type elementType) {
		this.elementType = elementType;
	}
	public override string FullName {
		get { return Name; }
	}
}

public class StructType: ClassType {
	public StructType(InputElement id, SymbolTable declSpace) : base(id, declSpace) {
	}
	override public bool IsReferenceType {
		get { return false; }
	}
	override public bool IsValueType {
		get { return true; }
	}
}

public class Type: Symbol {
	public System.Type type = null;
	public ClassType enclosingType = null;
	virtual public bool Equals(Type t) {
		if (this == t)
			return true;
		if (((object)this).GetType() != ((object)t).GetType())
			return false;
		return this.FullName == t.FullName;
	}
	static public bool Equals(Type t1, Type t2) {
		return t1.Equals(t2);
	}
	override public string FullName {
		get {
			if (declSpace == null)
				return Name;
			switch (base.FullName) {
			case "System.Boolean": return "bool";
			case "System.Byte":    return "byte";
			case "System.Char":    return "char";
			case "System.Decimal": return "decimal";
			case "System.Double":  return "double";
			case "System.Int16":   return "short";
			case "System.Int32":   return "int";
			case "System.Int64":   return "long";
			case "System.Object":  return "object";
			case "System.SByte":   return "sbyte";
			case "System.Single":  return "float";
			case "System.String":  return "string";
			case "System.UInt16":  return "ushort";
			case "System.UInt32":  return "uint";
			case "System.UInt64":  return "ulong";
			default: return base.FullName;
			}
		}
	}
	virtual public bool Implements(Type t) {
		return false;
	}
	virtual public bool InheritsFrom(Type t) {
		return this == t;
	}
	virtual public bool IsClass {
		get { return false; }
	}
	public bool IsFloating {
		get { return this.FullName == "float" || this.FullName == "double"; }
	}
	public bool IsNested {
		get { return enclosingType != null; }
	}
	public bool IsNumeric {
		get { return IsSigned || IsUnsigned || this.FullName == "char"
		          || IsFloating || this.FullName == "decimal"; }
	}
	virtual public bool IsReferenceType {
		get { return false; }
	}
	public bool IsScalarType {
		get { return IsReferenceType || IsNumeric || this.FullName == "bool"
			|| this is EnumType || this is PointerType; }
	}
	public bool IsSigned {
		get { return this.FullName == "sbyte" || this.FullName == "short"
		          || this.FullName == "int"   || this.FullName == "long"; }
	}
	public bool IsUnsigned {
		get { return this.FullName == "byte" || this.FullName == "ushort"
		          || this.FullName == "uint" || this.FullName == "ulong"; }
	}
	virtual public bool IsValueType {
		get { return false; }
	}
	override public string Kind {
		get {
			string s = base.Kind;
			if (s.EndsWith("type"))
				s = s.Substring(0, s.Length - 4);
			return s;
		}
	}
	virtual public string RealName {
		get {
			if (Name == "void")
				return "System.Void";
			else if (declSpace == null)
				return Name;
			return base.FullName;
		}
	}
	public int Size {
		get { return SizeOf(this); }
	}
	public int SizeOf(Type t) {
		switch (t.FullName) {
		case "sbyte": case "byte": return 1;
		case "short": case "ushort": case "char": return 2;
		case "int": case "uint": case "float": return 4;
		case "long": case "ulong": case "double": return 8;
		}
		return 0;
	}	
	public Type(InputElement id, SymbolTable declSpace) : base(id, declSpace) {}
	public Type(string name, SymbolTable declSpace) : base(name, declSpace) {}
	public Type() : base() {}
	override public void Write(TextWriter w) {
		w.Write("{0}", FullName);
	}
}

public class UnmanagedPointerType: PointerType {
	override public bool Equals(Type t) {
		return t is UnmanagedPointerType && elementType.Equals(((UnmanagedPointerType)t).elementType);
	}
	public override string Name {
		get { return elementType.Name + "*"; }
	}
	public override string RealName {
		get { return elementType.RealName + "*"; }
	}
	public UnmanagedPointerType(Type elementType) : base(elementType) { }
	override public void Write(TextWriter w) {
		elementType.Write(w);
		w.Write("*");
	}
}

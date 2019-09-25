using System;
using System.IO;
using System.Text;
using System.Diagnostics;
using System.Collections;

public class Block: Symbol {
	SymbolTable labels;
	public SymbolTable locals;
	public Constant AddConstant(InputElement id, MessageWriter msg) {
		Symbol s = LookupLocal(id);
		if (s != null)
			msg.Error(id, "constant '{0}' already defined in this or a parent scope at {1}",
				id.str, new Coordinate(s.id).ToString());
		Constant t = new Constant(id, locals);
		t.Add(id, locals, msg);
		return t;
	}
	public Label AddLabel(InputElement label, MessageWriter msg) {
		Label t = LookupLabel(label);
		if (t != null)
			msg.Error(label, "label '{0}' already defined at {1}", label.str,
				new Coordinate(t.id).ToString());
		t = new Label(label, labels);
		labels.Add(label.str, t);
		return t;
	}
	public Local AddLocal(InputElement id, MessageWriter msg) {
		Symbol s = LookupLocal(id);
		if (s != null)
			msg.Error(id, "local '{0}' already defined in this or a parent scope at {1}",
				id.str, new Coordinate(s.id).ToString());
		Local t = new Local(id, locals);
		t.Add(id, locals, msg);
		return t;
	}
	public Block(SymbolTable declSpace) : base((string)null, declSpace) {
		locals = new SymbolTable(this);
		labels = new SymbolTable(this);
	}
	override public string FullName {
		get { return declSpace.Owner.FullName; }
	}
	override public IEnumerator GetEnumerator() {
		return locals.GetEnumerator();
	}
	public Method GetMethod() {
		SymbolTable bindings = locals;
		while ((bindings = bindings.Owner.declSpace) != null)
			if (bindings.Owner is Method)
				return (Method)bindings.Owner;
		Debug.Fail("missing method");
		return null;
	}
	override public ClassType GetType() {
		return GetMethod().GetType();
	}
	override public Symbol Lookup(InputElement id, MessageWriter msg) {
		Symbol t = locals[id.str];
		if (t == null)
			t = declSpace.Owner.Lookup(id, msg);
		return t;
	}
	public Label LookupLabel(InputElement label) {
		Block b = this;
		do {
			Label t = b.labels[label.str] as Label;
			if (t != null)
				return t;
		} while ((b = b.declSpace.Owner as Block) != null);
		return null;
	}
	public Local LookupLocal(InputElement id) {
		Block b = this;
		do {
			Local t = b.locals[id.str] as Local;
			if (t != null)
				return t;
		} while ((b = b.declSpace.Owner as Block) != null);
		return null;
	}
}

public class Constant: Local {
	public object value = null;
	public Constant(InputElement id, SymbolTable declSpace) : base(id, declSpace) {
	}
}

public class Constructor: Method {
	public Constructor(InputElement id, SymbolTable declSpace) : base(id, declSpace) {}
}

public class EnumMember: Symbol {
	Type type;
	public object value = 0;
	public EnumMember(InputElement id, SymbolTable declSpace) : base(id, declSpace) {}
	override public bool IsAccessible(Type context) {
		return true;
	}
	override public Type Type {
		get { return type; }
		set { type = value; }
	}
}

public class Event: Field {
	public bool IsFieldLike = false;
	Method add;
	Method remove;
	new public Method Add {
		get { return add; }
		set { add = value; }
	}
	override public bool Equals(object o) {
		if (o is Event)
			return Equals((Event)o);
		return base.Equals(o);
	}
	public bool Equals(Event e) {
		return Name == e.Name
			&& Add.Equals(e.Add) && Remove.Equals(e.Remove);
	}
	public Event(InputElement id, SymbolTable declSpace) : base(id, declSpace) {
		ClassType c = (ClassType)declSpace.Owner;
		add = c.AddMethod(new InputElement(mangle(id.str, "add_"), id.coord), null);
		add.AddFormal(new InputElement("value", id.coord), null);
		remove = c.AddMethod(new InputElement(mangle(id.str, "remove_"), id.coord), null);
		remove.AddFormal(new InputElement("value", id.coord), null);
	}
	override public int GetHashCode() { return base.GetHashCode(); }
	override public bool IsVariable {
		get { return false; }
	}
	public Method Remove {
		get { return remove; }
		set { remove = value; }
	}
	override public Type Type {
		get { return type; }
		set {
			type = value;
			Add.signature.formals[0].Type = value;
			Remove.signature.formals[0].Type = value;
		}
	}
}

public class Field: Symbol {
	protected Type type = null;
	public Field(InputElement id, SymbolTable declSpace) : base(id, declSpace) {}
	override public bool IsVariable {
		get { return true; }
	}
	override public Type Type {
		get { return type; }
		set { type = value; }
	}
}

public class Formal: Local {
	public InputElement modifier = null;
	public bool IsParams = false;
	public Formal(InputElement id, SymbolTable declSpace) : base(id, declSpace) {}
	public Formal(InputElement id) : base(id, null) {}
	override public bool IsVariable {
		get { return true; }
	}
	override public string Kind {
		get { return modifier == null ? "formal" : "formal " + modifier; }
	}
}

public interface INamespaceOrType {
	Symbol Lookup(InputElement id, MessageWriter msg);
	Symbol Lookup(string id, MessageWriter msg);
	Symbol this[string id] { get; }
}

public class Label: Symbol {
	public labeled_statement definition;
	override public string FullName {
		get { return Name; }
	}
	public Label(InputElement id, SymbolTable declSpace) : base(id, declSpace) {}
}

public class Local: Symbol {
	int _ordinal = 0;
	protected Type type = null;
	bool writable = true;
	override public string FullName {
		get { return Name; }
	}
	override public ClassType GetType() {
		return declSpace.Owner.GetType();
	}
	override public bool IsInstance {
		get { return false; }
	}
	override public bool IsVariable {
		get { return writable; }
	}
	public Local(InputElement id, SymbolTable declSpace) : base(id, declSpace) {}
	virtual public int ordinal {
		get { return _ordinal; }
		set { _ordinal = value; }
	}
	public bool ReadOnly {
		get { return !writable; }
		set { writable = !value; }
	}
	override public Type Type {
		get { return type; }
		set { type = value; }
	}
}

public class Method: Symbol {
	public Method interfaceMethod = null;
	public SymbolTable locals;
	public Signature signature = new Signature();
	public Formal AddFormal(InputElement id, MessageWriter msg) {
		Formal f = new Formal(id, locals);
		f.Add(id, msg);
		signature.Add(f);
		return f;
	}
	public void AddFormals(FormalList formals, MessageWriter msg) {
		signature = new Signature(formals);
		foreach (Formal f in formals) {
			f.declSpace = locals;
			f.Add(f.id, msg);
		}
	}
	public int ArgCount {
		get { return signature.ArgCount; }
	}
	public override void Dump(TextWriter w) {
		base.Dump(w);
	}
	override public bool Equals(object o) {
		if (o is Method)
			return Equals((Method)o);
		return base.Equals(o);
	}
	public bool Equals(Method m) {
		return Name == m.Name
			&& signature.Type.Equals(m.signature.Type)
			&& signature.Equals(m.signature);
	}
	public override string FullName {
		get { return declSpace == null ? Name : base.FullName; }
	}
	public Method GetBaseDefinition() {
		if (Is("override")) {
			for (ClassType c = GetType(); c != null; c = c.baseClass) {
				Method m;
				Symbol t = c.members[id.str];
				if (t is MethodSuite
				&& (m = ((MethodSuite)t).Contains(signature)) != null
				&& !m.Is("override") && (m.Is("virtual") || m.Is("abstract")))
					return m;
			}
		}
		return this;
	}
	override public IEnumerator GetEnumerator() {
		return locals.GetEnumerator();
	}
	override public int GetHashCode() { return base.GetHashCode(); }
	public bool IsParams {
		get { return ArgCount > 0 ? signature.Last.IsParams : false; }
	}
	new public ClassType GetType() {
		return declSpace == null ? null : (ClassType)declSpace.Owner;
	}
	override public Symbol Lookup(InputElement id, MessageWriter msg) {
		Symbol t = locals[id.str];
		if (t == null)
			t = declSpace.Owner.Lookup(id, msg);
		return t;
	}
	public Method(InputElement id, SymbolTable declSpace) : base(id, declSpace) {
		locals = new SymbolTable(this);
	}
	public Formal this[int i] {
		get { return signature[i]; }
	}
	override public Type Type {
		get { return signature.Type; }
		set { signature.Type = value; }
	}
	override public void Write(TextWriter w) {
		signature.Type.Write(w);
		w.Write(" {0}", FullName);
		signature.Write(w);
	}
}

public class MethodSuite: Symbol {
	public MethodList methods = new MethodList();
	public Method Add(Method m) {
		methods.Add(m);
		return m;
	}
	public Method Contains(Method t) {
		foreach (Method m in methods)
			if (t.Equals(m))
				return m;
		return null;
	}
	public Method Contains(Signature sig) {
		foreach (Method m in methods)
			if (sig.Equals(m.signature))
				return m;
		return null;
	}
	public int Count {
		get { return methods.Count; }
	}
	public virtual Method FindMethod(params Type[] args) {
		foreach (Method m in methods)
			if (args.Length == m.ArgCount) {
				int i;
				for (i = 0; i < args.Length; i++)
					if (!Type.Equals(m[i].Type, args[i]))
						break;
				if (i == args.Length)
					return m;
			}
		return null;
	}
	override public string FullName {
		get {
			if (declSpace != null)
				return base.FullName;
			if (methods.Count == 1)
				return methods[0].FullName;
			StringBuilder sb = new StringBuilder();
			if (methods.Count > 0) {
				sb.Append('<');
				for (int i = 0; i < methods.Count; i++) {
					if (i > 0)
						sb.Append(',');
					sb.Append(methods[i].GetType().FullName);
				}
				sb.Append(">.");
			}
			sb.Append(Name);						
			return sb.ToString();
		}
	}
	override public IEnumerator GetEnumerator() {
		return methods.GetEnumerator();
	}
	override public bool IsAccessible(Type context) {
		if (declSpace != null)
			return base.IsAccessible(context);
		foreach (Method m in methods)
			if (m.IsAccessible(context))
				return true;
		return false;
	}
	public MethodSuite(InputElement id) : base(id) {}
	public MethodSuite(InputElement id, SymbolTable declSpace) : base(id, declSpace) {}
	override public Type Type {
		get { return methods[0].Type; }
		set {
			foreach (Method m in methods)
				m.Type = value;
		}
	}
	public Method this[int i] {
		get { return methods[i]; }
	}
	override public void Write(TextWriter w) {
		foreach (Method m in methods)
			m.WriteLine(w);
	}
	override public void WriteLine(TextWriter w) {
		Write(w);
	}
}

public class NameSpace: Symbol, INamespaceOrType {
	public Imports imports = null;
	public BuiltinTypes Types;
	public stringList aliases = new stringList();
	public SymbolList usingdirectives;
	public SymbolTable members;
	override public string FullName {
		get { return declSpace == null ? "" : base.FullName; }
	}
	override public IEnumerator GetEnumerator() {
		return members.GetEnumerator();
	}
	public Symbol Import(string fullname) {
		if (imports != null)
			return imports.Import(fullname);
		if (declSpace != null)
			return ((NameSpace)declSpace.Owner).Import(fullname);
		return null;
	}
	override public bool IsAccessible(Type context) {
		return true;
	}
	override public string Kind {
		get { return (Name == "" ? "global " : "") + "namespace"; }
	}
	public Symbol Lookup(string fullname) {
		SymbolTable bindings = this.members;
		string[] names = fullname.Split('.');
		for (int i = 0; i < names.Length - 1; i++) {
			NameSpace t = bindings[names[i]] as NameSpace;
			if (t == null)
				return null;
			bindings = t.members;
		}
		return bindings[names[names.Length-1]];
	}
	override public Symbol Lookup(InputElement id, MessageWriter msg) {
		Symbol t = this[id.str];
		if (t == null)
			t = searchUsing(id, msg);
		if (t != null)
			return t;
		else if (declSpace != null)
			return declSpace.Owner.Lookup(id, msg);
		return null;
	}
	override public Symbol LookupType(InputElement id, MessageWriter msg) {
		Symbol t = this[id.str];
		if (!(t is INamespaceOrType))
			t = searchUsing(id, msg);
		if (t is INamespaceOrType)
			return t;
		else if (declSpace != null)
			return declSpace.Owner.LookupType(id, msg);
		return null;
	}
	public NameSpace(Imports imports) {
		members = new SymbolTable(this);
		this.imports = imports;
		this.Types = new BuiltinTypes(imports);
	}
	public NameSpace(string name, SymbolTable declSpace) : base(name, declSpace) {
		members = new SymbolTable(this);
	}
	public NameSpace(InputElement id, SymbolTable declSpace) : base(id, declSpace) {
		members = new SymbolTable(this);
	}
	public Symbol this[string id] {
		get {
			Symbol t = members[id];
			if (t == null && FullName != "")
				t = Import(FullName + "." + id);
			else if (t == null)
				t = Import(id);
			return t;
		}
	}
	Symbol searchUsing(InputElement id, MessageWriter msg) {
		int count = 0;
		Symbol t = null;
		if (usingdirectives != null)
			foreach (NameSpace n in usingdirectives)
				if (n[id.str] != null) {
					count++;
					if (t == null)
						t = n[id.str];
				}
		if (count > 1)
			msg.Error(id, "'{0}' is ambiguous", id.str);
		return t;
	}
}

public class Property: Symbol {
	Method get;
	Method set;
	public Method AddGet(InputElement id) {
		ClassType c = (ClassType)declSpace.Owner;
		get = c.AddMethod(new InputElement(mangle(id.str, "get_"), id.coord), null);
		return get;
	}
	public Method AddSet(InputElement id) {
		ClassType c = (ClassType)declSpace.Owner;
		set = c.AddMethod(new InputElement(mangle(id.str, "set_"), id.coord), null);
		set.AddFormal(new InputElement("value", id.coord), null);
		return set;
	}
	override public bool Equals(object o) {
		if (o is Property)
			return Equals((Property)o);
		return base.Equals(o);
	}
	public bool Equals(Property p) {
		if (Name != p.Name)
			return false;
		if (Get == null && p.Get != null || Get != null && p.Get == null
		||  Set == null && p.Set != null || Set != null && p.Set == null)
			return false;
		return (Get == null || Get.Equals(p.Get)) && (Set == null || Set.Equals(p.Set));
	}
	public Method Get {
		get { return get; }
		set { get = value; }
	}
	override public int GetHashCode() { return base.GetHashCode(); }
	new public ClassType GetType() {
		return (ClassType)declSpace.Owner;
	}
	override public Symbol Lookup(InputElement id, MessageWriter msg) {
		throw new InvalidOperationException(id.str);
	}
	override public Symbol LookupType(InputElement id, MessageWriter msg) {
		throw new InvalidOperationException(id.str);
	}
	public Property(InputElement id, SymbolTable declSpace) : base(id, declSpace) {
	}
	public Method Set {
		get { return set; }
		set { set = value; }
	}
	override public Type Type {
		get {
			if (Get != null)
				return Get.Type;
			if (Set != null)
				return Set.signature.formals[0].Type;
			return null;
		}
		set {
			if (Get != null)
				Get.Type = value;
			if (Set != null)
				Set.signature.formals[0].Type = value;
		}
	}
}

public class Signature {
	public FormalList formals;
	Type returnType;
	public void Add(Formal f) {
		formals.Add(f);
	}
	public int ArgCount {
		get { return formals.Count; }
	}
	override public bool Equals(object o) {
		if (o is Signature)
			return Equals((Signature)o);
		return base.Equals(o);
	}
	public bool Equals(Signature sig) {
		return Equals(this, sig);
	}
	public static bool Equals(Signature s1, Signature s2) {
		if (s1.ArgCount != s2.ArgCount)
			return false;
		for (int i = 0; i < s1.ArgCount; i++)
			if (!Type.Equals(s1[i].Type, s2[i].Type)
			|| s1[i].modifier != s2[i].modifier)
				return false;
		return true;
	}
	public IEnumerator GetEnumerator() {
		return formals.GetEnumerator();
	}
	override public int GetHashCode() { return base.GetHashCode(); }
	public Formal Last {
		get { return ArgCount > 0 ? formals[ArgCount-1] : null; }
	}
	public Signature(FormalList formals) {
		this.formals = formals;
	}
	public Signature() : this(new FormalList()) {}
	public Formal this[int i] {
		get { return formals[i]; }
	}
	public override string ToString() {
		return String.Format("{0}#{1}", base.ToString(), GetHashCode());
	}
	public Type Type {
		get { return returnType; }
		set { returnType = value; }
	}
	public void Write(TextWriter w) {
		w.Write("(");
		for (int i = 0; i < formals.Count; i++) {
			if (i > 0)
				w.Write(",");
			if (formals[i].modifier != null)
				w.Write("{0} ", formals[i].modifier.str);
			if (formals[i].IsParams)
				w.Write("params ");
			formals[i].Type.Write(w);
		}
		w.Write(")");
	}
	public void WriteLine(TextWriter w) {
		Write(w);
	}
}

public abstract class Symbol: SymbolRoot  {
	public string module = null;
	public attribute_sectionList attributes = null;
	public SymbolTable declSpace = null;
	public InputElement id = null;
	protected stringList modifiers = null;
	static public Symbol Add(InputElement id, Symbol s, SymbolTable bindings, MessageWriter msg) {
		if (bindings.Contains(id.str)) {
			string name = bindings.Owner.FullName;
			if (name.Length > 0)
				name = " '" + name + "'";
			msg.Error(id, "{0}{1} already contains a definition for '{2}'", bindings.Owner.Kind, name, id.str);
		} else
			bindings.Add(id.str, s);
		return s;
	}
	public Symbol Add(InputElement id, SymbolTable bindings, MessageWriter msg) {
		return Add(id, this, bindings, msg);
	}
	public Symbol Add(InputElement id, MessageWriter msg) {
		return Add(id, this, declSpace, msg);
	}
	public void AddAttribute(string target, attribute attr) {
		AddAttributes(new attribute_section(new InputElement(target), attributeList.New(attr)));
	}
	public void AddAttributes(attribute_section attr) {
		if (attributes == null)
			attributes = attribute_sectionList.New();
		foreach (attribute_section s in attributes)
			if (s.target == attr.target) {
				s.attributes.AddRange(attr.attributes);
				return;
			}
		attribute_section x = new attribute_section(attr.target, attributeList.New());
		x.attributes.AddRange(attr.attributes);
		attributes.Add(x);
	}
	public void AddAttributes(attribute_sectionList list) {
		foreach (attribute_section x in list)
			AddAttributes(x);
	}
	public void Dump() {
		Dump(Console.Error);
	}
	public virtual void Dump(TextWriter w) {
		Debug.Dump(this, w);
	}
	virtual public string FullName {
		get { return GetFullName(Name, declSpace); }
	}
	virtual public IEnumerator GetEnumerator() {
		throw new InvalidOperationException();
	}
	static public string GetFullName(string name, SymbolTable bindings) {
		Debug.Assert(bindings != null);
		if (bindings.Owner == null)
			Debug.Fail("orphan symbol table");
		if (bindings.Owner.FullName != "")
			return bindings.Owner.FullName + "." + name;
		else
			return name;
	}
	public NameSpace GetNameSpace() {
		return GetNameSpace(declSpace);
	}
	static public NameSpace GetNameSpace(SymbolTable bindings) {
		while (!(bindings.Owner is NameSpace))
			bindings = bindings.Owner.declSpace;
		return (NameSpace)bindings.Owner;
	}
	new public virtual ClassType GetType() {
		return (ClassType)declSpace.Owner;
	}
	virtual public bool Is(string mod) {
		return Modifiers.Contains(mod);
	}
	virtual public bool IsAccessible(Type context) {
		Type t = declSpace.Owner as Type;
		if (t != null && !t.IsAccessible(context))
			return false;
		if (Is("public"))
			return true;
		if (Is("internal"))
			return true;
		if (Is("protected")) {
			for ( ; context != null; context = context.enclosingType)
				if (context.InheritsFrom(t))
					return true;
			return false;
		}
		if (Is("private"))
			return context == t;
		return false;
	}
	virtual public int IsAny(params string[] mods) {
		int count = 0;
		foreach (string mod in mods)
			if (Is(mod))
				count++;
		return count;
	}
	virtual public bool IsInstance {
		get { return !IsStatic; }
	}
	virtual public bool IsPublic {
		get { return Is("public"); }
	}
	virtual public bool IsStatic {
		get { return Is("static"); }
	}
	virtual public bool IsVariable {
		get { return false; }
	}
	virtual public string Kind {
		get { return base.GetType().Name.ToLower(); }
	}
	virtual public Symbol Lookup(InputElement id, MessageWriter msg) {
		return declSpace.Owner.Lookup(id, msg);
	}
	virtual public Symbol Lookup(string id, MessageWriter msg) {
		return Lookup(new InputElement(id), msg);
	}
	virtual public Symbol LookupType(InputElement id, MessageWriter msg) {
		return declSpace.Owner.LookupType(id, msg);
	}
	static protected string mangle(string id, string prefix) {
		int i = id.LastIndexOf('.');
		if (i >= 0)
			return id.Substring(0, i+1) + prefix + id.Substring(i+1);
		else
			return prefix + id;
	}
	virtual public stringList Modifiers {
		get {
			if (modifiers == null)
				modifiers = new stringList();
			return modifiers;
		}
		set { modifiers = value; }
	}
	virtual public string Name {
		get { return id.str == null ? "" : id.str; }
		set { id.str = value; }
	}
	protected Symbol() : this("", null) {}
	protected Symbol(InputElement id) : this(id, null) {}
	protected Symbol(string name, SymbolTable declSpace) : this(new InputElement(name), declSpace) {}
	protected Symbol(InputElement id, SymbolTable declSpace) {
		this.id = id;
		this.declSpace = declSpace;
	}
	public override string ToString() {
		return String.Format("{0}#{1}", base.ToString(), GetHashCode());
	}
	virtual public Type Type {
		get {
			Debug.Fail(String.Format("{0} {1} does not have a Type", Kind, FullName));
			throw new InvalidOperationException();
		}
		set {
			Debug.Fail(String.Format("{0} {1} does not have a Type", Kind, FullName));
			throw new InvalidOperationException();
		}
	}
	virtual public void Write(TextWriter w) {}
	virtual public void WriteLine(TextWriter w) {
		Write(w);
		w.WriteLine();
	}
}

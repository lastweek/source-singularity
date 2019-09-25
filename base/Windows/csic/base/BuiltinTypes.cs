public class BuiltinTypes {
	Imports imp;
	public MessageWriter msg = null;

	public BuiltinTypes(Imports imp) {
		this.imp = imp;
	}
	public BuiltinTypes(Imports imp, MessageWriter msg) : this(imp) {
		this.msg = msg;
	}
	ClassType Builtin(string fullname) {
		ClassType t = (ClassType)imp.Import(fullname);
		if (t == null && msg != null) {
			msg.Error("unknown built-in type '{0}'; maybe a missing -reference option", fullname);
			return new ClassType(new InputElement(fullname), null);			
		}
		Debug.Assert(t != null);
		return t;
	}
	public ClassType Array   { get { return Builtin("System.Array"); } }
	public ClassType Bool    { get { return Builtin("System.Boolean"); } }
	public ClassType Byte    { get { return Builtin("System.Byte"); } }
	public ClassType Char    { get { return Builtin("System.Char"); } }
	public ClassType Decimal { get { return Builtin("System.Decimal"); } }
	public ClassType Delegate{ get { return Builtin("System.Delegate"); } }
	public ClassType Double  { get { return Builtin("System.Double"); } }
	public ClassType Enum    { get { return Builtin("System.Enum"); } }
	public ClassType Exception
			{ get { return Builtin("System.Exception"); } }
	public ClassType Float   { get { return Builtin("System.Single"); } }
	public ClassType Short   { get { return Builtin("System.Int16"); } }
	public ClassType ICloneable
			{ get { return Builtin("System.ICloneable"); } }
	public ClassType IDisposable
			{ get { return Builtin("System.IDisposable"); } }
	public ClassType IEnumerable
			{ get { return Builtin("System.Collections.IEnumerable"); } }
	public ClassType Int     { get { return Builtin("System.Int32"); } }
	public ClassType IntPtr  { get { return Builtin("System.IntPtr"); } }
	public ClassType Long    { get { return Builtin("System.Int64"); } }
	public ClassType Monitor { get { return Builtin("System.Threading.Monitor"); } }
	public ClassType MulticastDelegate
			{ get { return Builtin("System.MulticastDelegate"); } }
	public ClassType Null = new ClassType(new InputElement("null"), null);
	public ClassType Object  { get { return Builtin("System.Object"); } }
	public ClassType RuntimeArgumentHandle
			{ get { return Builtin("System.RuntimeArgumentHandle"); } }
	public ClassType RuntimeTypeHandle
			{ get { return Builtin("System.RuntimeTypeHandle"); } }
	public ClassType SByte   { get { return Builtin("System.SByte"); } }
	public ClassType String  { get { return Builtin("System.String"); } }
	public ClassType Type    { get { return Builtin("System.Type"); } }
 	public ClassType TypedReference { get { return Builtin("System.TypedReference"); } }
	public ClassType UShort  { get { return Builtin("System.UInt16"); } }
	public ClassType UInt    { get { return Builtin("System.UInt32"); } }
	public ClassType ULong   { get { return Builtin("System.UInt64"); } }
	public ClassType UIntPtr { get { return Builtin("System.UIntPtr"); } }
	public ClassType ValueType
			{ get { return Builtin("System.ValueType"); } }
	public Type Void = new Type("void", null);
}

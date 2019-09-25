using System;

public class InputElement: IHasCoordinate, IComparable, ICloneable, IImage {
	public Coordinate coord;
	private Coordinate _end;
	public string str;
	public string tag;

	public Coordinate begin {
		get { return coord; }
		set { coord = value; }
	}
	public InputElement Clone(string str) {
		return new InputElement(tag, str, coord);
	}
	public int CompareTo(string s) {
		return str.CompareTo(s);
	}
	public Coordinate end {
		get { return _end; }
		set { _end = value; }
	}
	override public bool Equals(object o) {
		if (o is InputElement)
			return ((InputElement)o).str == str;
		else if (o is string)
			return (string)o == str;
		else
			return false;
	}
	override public int GetHashCode() {
		return str.GetHashCode();
	}
	public InputElement(string tag, string str, string file, int lineno, int colno) {
		this.tag = tag;
		this.str = str;
		_end.file = coord.file = file;
		_end.line = coord.line = lineno;
		coord.column = colno;
		_end.column = colno + (str != null ? str.Length : 0);
	}
	public InputElement(string tag, string str, string file, int lineno, int colno,
		string originalFile, int fileOffset) : this(tag, str, file, lineno, colno) {
		coord.originalFile = originalFile;
		coord.fileOffset = fileOffset;
	}
	public InputElement(string tag, string str, Coordinate coord) : this(tag, str, coord.file, coord.line, coord.column) { }
	public InputElement(string str) : this(str, str, "", 0, 0) {}
	public InputElement(string str, Coordinate coord) : this(str, str, coord) {}
	override public string ToString() {
		string s = "InputElement(" + tag;
		if (str != tag)
			s += "," + str;
		return s + ")";
	}

	// ICloneable
	object ICloneable.Clone() {
		return Clone(str);
	}

	// IComparable
	int IComparable.CompareTo(object o) {
		if (o is InputElement)
			return str.CompareTo(((InputElement)o).str);
		throw new ArgumentException();
	}

	// IImage
	string IImage.Image() {
		if (str == tag && coord.line == 0 && coord.column == 0)
			return str;
		else
			return Debug.Image(this);
	}
}

public class MalformedInputElement : InputElement {
	InputElement error;

	public MalformedInputElement(InputElement error)
		: base("MALFORMED", error.str, error.coord) {
		this.error = error;
	}
}

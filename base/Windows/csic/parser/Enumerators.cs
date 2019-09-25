public abstract class CharEnumerator {
	abstract public char Current { get; }
	abstract public bool MoveNext();
	abstract public void Reset();
	abstract public int Location { get; }
}


public class String2CharEnumerator : CharEnumerator {
	private string text;
	private int i=-1;
	public String2CharEnumerator(string text) {
		this.text = text;
	}

	override public char Current { 
		get {
			try {
				return text[i];
			} catch (System.Exception) {
				throw new System.InvalidOperationException();
			}
		}
	}
	override public int Location { 
		get {
			return i;
		}
	}
	override public bool MoveNext() {
		i++;
		return i < text.Length;
	}
	override public void Reset() {}
}

public class File2CharEnumerator : CharEnumerator {
	private System.IO.TextReader reader;
	public File2CharEnumerator(System.IO.TextReader reader) {
		this.reader = reader;
	}

	private char _current;
	override public char Current { 
		get {
			return _current;
		}
	}
	private int _location = -1;
	override public int Location { 
		get {
			return _location;
		}
	}
	override public bool MoveNext() {
		int c = reader.Read();
		if (c == -1)
			return false;
		_location++;
		_current = (char)c;
		return true;
	}
	override public void Reset() {}
}

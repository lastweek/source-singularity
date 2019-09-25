using System;
using System.IO;

public class MessageWriter {
	public int Count = 0;
	public TextWriter Out;
	public MessageWriter() : this(Console.Out) {}
	public MessageWriter(TextWriter Out) { this.Out = Out; }
	public void Error(string fmt, params string[] args) {
		Out.WriteLine(fmt, args);
		Count++;
	}
	public void Error(Coordinate src, string fmt, params string[] args) {
		if (src.line > 0)
			Out.Write("{0}: ", src);
		Out.WriteLine(fmt, args);
		Count++;
	}
	public void Error(InputElement token, string fmt, params string[] args) {
		Error(new Coordinate(token), fmt, args);
	}
	public void Warning(string fmt, params string[] args) {
		Out.Write("Warning: ");
		Out.WriteLine(fmt, args);
	}
	public void Warning(Coordinate src, string fmt, params string[] args) {
		if (src.line > 0)
			Out.Write("{0}: ", src);
		Warning(fmt, args);
	}
	public void Warning(InputElement token, string fmt, params string[] args) {
		Warning(new Coordinate(token), fmt, args);
	}
	public void Write(string fmt, params object[] args) {
		Out.Write(fmt, args);
	}
	public void WriteLine(string fmt, params object[] args) {
		Out.WriteLine(fmt, args);
	}
	public void WriteLine() {
		Out.WriteLine();
	}
}

public struct Coordinate {
	public string originalFile;
	public int fileOffset;

	public string file;
	public int line, column;
	public Coordinate(string file, int line, int column, string originalFile, int fileOffset) {
		this.file = file;
		this.line = line;
		this.column = column;
		this.originalFile = originalFile;
		this.fileOffset = fileOffset;
	}
	public Coordinate(InputElement token) : this(token.coord.file, token.coord.line, token.coord.column, token.coord.originalFile, token.coord.fileOffset) {}
	override public string ToString() {
		return String.Format("{0}({1},{2})", file, line, column);
	}
	
}

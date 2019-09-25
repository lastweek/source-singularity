using System;
using System.IO;
using System.Collections;

public class NullReader: IImportReader {
	NameSpace global;
	MessageWriter msg;

	public Symbol Import(string fullname) {
		return null;
	}
	public void Init(NameSpace global, MessageWriter msg) {
		this.global = global;
		this.msg = msg;
	}
	public bool Load(string path) {
		return false;
	}
	public SymbolList Lookup(string name, stringList namespaces) {
		return new SymbolList();
	}
	public NullReader() {}
}

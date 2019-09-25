using System;
using System.IO;
using System.Collections;

public interface IImportReader {
	SymbolList Lookup(string name, stringList namespaces);
	Symbol Import(string fullname);
	void Init(NameSpace global, MessageWriter msg);
	bool Load(string path);
}

public class Imports: IImage {
	public NameSpace global;
	IImportReader reader;
	protected MessageWriter msg;
	stringList libdirs = new stringList();
	ArrayList loaded = new ArrayList();

	public void Add(string dir) {
		if (!libdirs.Contains(dir))
			libdirs.Add(dir);
	}
	public string Image() {
		return String.Format("{0}#{1}", ToString(), GetHashCode());
	}
	public Imports(IImportReader reader, MessageWriter msg) {
		this.reader = reader;
		this.msg = msg;
		global = new NameSpace(this);
		reader.Init(global, msg);
	}
	public Symbol Import(string fullname) {
		Symbol sym = global.Lookup(fullname);
		if (sym != null)
			return sym;
		sym = reader.Import(fullname);
		if (sym != null)
			return sym;
		return null;
	}
	public stringList LibDirs { get { return libdirs; } }
	public bool Load(string file) {
		return LoadMetaData(file, libdirs);
	}
	bool LoadMetaData(string file, stringList libdirs) {
		foreach (string dir in libdirs) {
			string path = dir + "\\" + file;
			if (loaded.Contains(path.ToLower()))
				return true;
			if (reader.Load(path)) {
				loaded.Add(path.ToLower());
				return true;
			}
		}
		return false;			
	}
	public SymbolList Lookup(string name, stringList namespaces) {
		SymbolList list = reader.Lookup(name, namespaces);
		if (list != null)
			return list;
		return null;
	}
}

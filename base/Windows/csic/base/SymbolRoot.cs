using System;
using System.Collections;

abstract public class SymbolRoot: ICloneable {
	public int serial;
	static int nextserial = 0;
	public SymbolRoot() { serial = ++nextserial; }

	object ICloneable.Clone() { return MemberwiseClone(); }
	public SymbolRoot Clone() { return (SymbolRoot)((ICloneable)this).Clone(); }
}

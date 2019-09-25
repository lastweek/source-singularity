using System;
using System.Collections;
class Test {
	public static void Main() {}
	class Symbol  {}
	struct Segment {}
	static void popSegment() {}
	static ArrayList Symbols;
	public static void Foo(object o) {
		typeswitch (o) {
		case Int32  (x): Console.WriteLine(x); break;
		case Symbol (s): Symbols.Add(s); break;
		case Segment: popSegment(); break;
		default: throw new ArgumentException();
		}
	}
}

//
//if (o is Int32) { int x = (int)o; Console.WriteLine(x); }
//else if (o is Symbol) { Symbol s = (Symbol)o; Symbols.Add(s); }
//else if (o is Segment) { popSegment(); }
//else { throw new InvalidArgument(); }
//


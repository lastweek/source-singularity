using N;

namespace N {
using System;
using XX = System.Console;

class A {
	protected internal void f() { XX.WriteLine("A.f()"); }
	protected internal static void g() { System.Console.WriteLine("A.g()"); }
	public class X {}
	public static X x;
}
class B: A {
	new public int f = '3';
	public new static void g() { XX.WriteLine("B.g()"); A.x = new X(); }
}
}

class test {
	public static System.IO.TextWriter w = System.Console.Out;
	public static void Main() {
		B a = new B();
		w.WriteLine("a.f={0}", a.f);
		((A)a).f();
		A.g();
		B.g();
		w.WriteLine("A.x={0}", A.x);
	}
}

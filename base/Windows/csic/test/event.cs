using System;
public delegate void E(object sender, string msg);
class T {
	public event E x;
	public static event E y;
	public void fire(string s) {
		x("x", s);
		y("y", s);
	}
	public void F(E handler) {
		x += handler;
		y += handler;
	}
}
class U {
	static public void handler(object sender, string msg) {
		Console.WriteLine("{0}: {1}", sender, msg);
	}
	static public void Main() {
		T t = new T();
		t.x += new E(handler);
		t.F(new E(handler));
		t.fire("fire!");
	}
}

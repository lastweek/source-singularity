using System;
public delegate void E(object sender, string msg);
interface I {
	event E a;
}
class T: I {
	E _x;
	event E I.a {
		add { _x += value; }
		remove { _x -= value; }
	}
	public static event E y;
	public void fire(string s) {
		_x("x", s);
		y("y", s);
	}
	public void F(E handler) {
		((I)this).a += handler;
		y += handler;
	}
}
class U {
	static public void handler(object sender, string msg) {
		Console.WriteLine("{0}: {1}", sender, msg);
	}
	static public void Main() {
		T t = new T();
		((I)t).a += new E(handler);
		t.F(new E(handler));
		t.fire("fire!");
	}
}

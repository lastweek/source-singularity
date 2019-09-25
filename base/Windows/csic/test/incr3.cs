using System;
class T {
	static int _x;
	static int x {
		get { return _x; }
		set { _x = value; }
	}
	int _y;
	int y {
		get { return _y; }
		set { _y = value; }
	}
	static public void Main() {
		T.x += 1;
		Console.WriteLine("{0}", T.x++);
		Console.WriteLine("{0}", ++T.x);
		int u = 0, v = 1;
		f(new T(), ref u, out v);
		Console.WriteLine("{0} {1}", u, v);
	}
	static void f(T o, ref int a, out int b) {
		a = o.y += 1;
		Console.WriteLine("{0}", o.y++);
		Console.WriteLine("{0}", ++o.y);
		b = 0;
	}
}

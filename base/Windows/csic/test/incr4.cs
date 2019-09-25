using System;
class T {
	int x = 5, y = 6;
	static public void Main() {
		T[] x = new T[4] { null, new T(), new T(), new T() };
		x[1] = new T();
		int i = 1;
		Console.WriteLine("{0}", x[i++].x++);
		Console.WriteLine("{0}", i);
		f(ref x[++i].x, out x[i].y);
		Console.WriteLine("{0}", x[i].x);
		Console.WriteLine("{0}", x[i].y);
	}
	static void f(ref int a, out int b) {
		a += 2;
		b = 0;
		--b;
	}
}

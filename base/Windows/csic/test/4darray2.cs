using System;
struct X {
	public int a, b;
	public X(int a, int b) { this.a = a; this.b = b; }
}
class T {
	static public void print(X x) { Console.WriteLine("({0},{1})", x.a, x.b); }
	static public void Main() {
		X[,,,] a = new X[5,5,5,5];
		f(ref a[1,2,3,4], out a[4,3,2,1]);
		a[4,4,4,4]=a[1,2,3,4];
		print(a[1,2,3,4]);
		print(a[4,3,2,1]);
	}
	static void f(ref X a, out X b) {
		a.a += 1; a.b = -1;
		b = new X(1,2);
	}
}

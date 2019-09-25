using System;
struct X {
	public int a, b;
	public X(int a, int b) { this.a = a; this.b = b; }
}
class T {
	static public void print(int x) { Console.WriteLine("{0}", x); }
	static public void Main() {
		int[,,,] a = new int[5,5,5,5];
		f(ref a[1,2,3,4], out a[4,3,2,1]);
		a[4,4,4,4]=a[1,2,3,4];
		print(a[1,2,3,4]);
		print(a[4,3,2,1]);
		int sum = 0;
		foreach (int i in a)
			sum += i;
		Console.WriteLine("{0} {1}", sum, a.Length);
	}
	static void f(ref int a, out int b) {
		a += 1;
		b = 2;
	}
}

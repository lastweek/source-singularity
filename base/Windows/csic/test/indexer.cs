using System;
class T {
	int x;
	public int this[int a, T b] {
		get { return a+x; }
		set { x=b.x=value; }
	}
	public T(int x) { this.x = x; }
	public void print() { Console.WriteLine("{0}", x); }
	static public void Main() {
		T a = new T(1), b = new T(10);
		a.print(); b.print();
		Console.WriteLine("{0}", a[2,b]);
		a[2,b] = 20;
		a.print(); b.print();
		Console.WriteLine("{0}", a[2,b]++);
		b.print();
		a[2,b] += 5;
		a.print(); b.print();
	}
}

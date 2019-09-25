using System;
delegate void D(int x);
class A {
	public static void A1(int i) { Console.WriteLine("A1: {0}", i); }
	public void A2(int i) { Console.WriteLine("A2: {0}", i); }
}
class T {
	public static void Main() {
		D x = new D(A.A1);
		x(1);
		A t = new A();
		D y = new D(t.A2);
		y(2);
		D z = new D(y);
		z(3);
		D q = x + y; q(11);
		q += z; q(12);
		q -= x; q(13);
		D r = new D(q - y + x); r(14);
	}
}
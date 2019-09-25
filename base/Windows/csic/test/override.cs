class A {
	public virtual string Identity() { return "A.Identity(): " + ToString(); }
	public void print() { System.Console.WriteLine(Identity()); }
}
class B: A {
	override public string ToString() { return "B.ToString()"; }
	override public string Identity() { return "B.Identity(): " + base.ToString(); }
}
class test {
	public static void Main() {
		A a = new A();
		a.print();
		B b = new B();
		b.print();
		System.Console.WriteLine("{0}", ((A)b).Identity());
		System.Console.WriteLine("{0}", b.Identity());
		((A)b).print();
	}
}

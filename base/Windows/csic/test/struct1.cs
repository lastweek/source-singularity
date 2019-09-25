public class Test {
	static char cs='G';
	public char ci;

	public Test(char x) {
		ci=x;
	}

	public static void Main() {
		char c='D';
		System.Console.WriteLine(c);
		System.Console.WriteLine(c.ToString());
		char[] ca=new char[] { 'F', 'H'};
		System.Console.WriteLine(ca[1].ToString());
		System.Console.WriteLine(cs.ToString());
		Test t=new Test('B');
		System.Console.WriteLine(t.ci.ToString());
	}
}

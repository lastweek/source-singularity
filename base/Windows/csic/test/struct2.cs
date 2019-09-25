using System;

struct Sky {
	public int sun;
	public int rain;
}

public class Test {
	Sky sky;

	public int F() {
		return G();
	}
	public int G() {
		sky.sun=30;
		sky.rain=70;
		Console.WriteLine(sky.ToString());
		Console.WriteLine(sky.sun.ToString());
		return(sky.rain);
	}
	public static int Main() {
		Test t=new Test();
		return t.F();
	}

}

enum Color { Red, Green=2, Blue };
class test {
	static Color y = Color.Green;
	static test() {}
	public static void Main() {
		Color x = y;
		System.Console.WriteLine("{0}={1}", x, (int)x);
	}
}

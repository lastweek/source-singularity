struct Sky {
	public int sun;
	public int rain;
	public override string ToString() { return base.ToString(); }
}
class test {
	public static void Main() {
		int x = 10;
		System.Console.WriteLine(x.ToString());
		Sky y = new Sky();
		System.Console.WriteLine(y.ToString());
	}
}

public class test {
	bool[] x = new bool[10];
	public static void Main() {
		test t = new test();
		Emit(t.x[1]);
	}
	public static void Emit(bool flag) {
		System.Console.WriteLine(flag);
	}
}

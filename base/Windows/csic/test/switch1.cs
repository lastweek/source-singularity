class T {
	public static void f(int x) {
		switch (x) {
			case 1: x = 1; goto case 4;
			case -2: x = 2; break;
			default: System.Console.WriteLine(x); break;
			case 4: x = 5; goto default;
		}
	}
	public static void Main() {
		f(1);
	}
}
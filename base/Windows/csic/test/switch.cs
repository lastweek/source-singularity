class T {
	public static void f(int x) {
		switch (x) {
			case 1: x = 1; break;
			case -2: x = 2; break;
			default: System.Console.WriteLine(x); break;
			case 4: x = 5; break;
		}
	}
	public static int g(string x) {
		int y;
		switch (x) {
			case "hi": y = 1; break;
			case "there": y = 2; break;
			default: y = 3; break;
			case "you": y = 5; break;
		}
		return y;
	}
	public static void Main() {
		f(2);
		System.Console.WriteLine(g("hi"));
	}
}
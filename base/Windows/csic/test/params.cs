public class test {
	public int this[params string[] args] {
		get { return 1; }
		set { print(args); System.Console.WriteLine("value={0}", value); }
	}
	static void print(params string[] args) {
		if (args.Length == 0)
			System.Console.WriteLine("no arguments");
		else
			foreach (string s in args)
				System.Console.Write(s);
	}
	static public void Main() {
		print("Hello", " ", "World", "\n");
		print(new string[] {"Hello", " ", "World", "\n"});
		test x = new test();
		x["Hello", " ", "World", "\n"] = 2;
		print();
	}
}
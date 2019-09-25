class T {
	static int[] x;
	static public void Main() {
		x = new int[5];
		x[f(1)] = x[f(2)] += f(3);
		++x[f(3)];
		x[f(4)]++;
		print(x);
	}
	static int f(int i) {
		System.Console.WriteLine(i);
		return i;
	}
	static void print(int[] x) {
		for (int i = 0; i < x.Length; i++)
			System.Console.Write(x[i]);
		System.Console.WriteLine();
	}
		
}

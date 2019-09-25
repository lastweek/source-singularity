class T {
	public int i = 0, x = 0, y = 0;
	public int[] a = new int[10];
	public static void Main() {
		T t = new T();
		t.test();
		foreach (int x in t.a)
			System.Console.Write(" {0}", x);
		System.Console.WriteLine();
	}
	public void test() {
		//int[] a = new int[10]; int i = 0, x = 0, y = 0;
		x += 1;
		a[f(i)] += i;
		i++; x = i++;
		a[f(i)]++; y = a[f(i)]++;
		--i; x = --i;
		--a[f(i)]; y = --a[f(i)];
	}
	public int f(int x) {
		i = 6;
		return x;
	}
}

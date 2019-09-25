class EightQueens {
	static bool[]
		up =  { true, true, true, true, true, true, true, true, true, true, true, true, true, true, true },
		down = (bool[])up.Clone(),
		rows = new bool[8] { true, true, true, true, true, true, true, true };
	static public void Main() {
		for (int i = 0; i < up.Length; i++)
			up[i] = down[i] = true;
		for (int i = 0; i < rows.Length; ++i)
			rows[i] = true;
		queens(0, new int[8]);
	}
	static void queens(int c, int[] x) {
		for (int r = 0; r < rows.Length; r++)
			if (rows[r] && up[r-c+7] && down[r+c]) {
				rows[r] = up[r-c+7] = down[r+c] = false;
				x[c] = r;
				if (c == 7)
					print(x);
				else
					queens(c + 1, x);
				rows[r] = up[r-c+7] = down[r+c] = true;
			}
	}
	static void print(int[] x) {
		foreach (int c in x)
			System.Console.Write("{0}", c + 1);
		System.Console.WriteLine();
	}
}

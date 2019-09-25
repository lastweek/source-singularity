public class test {
	static int[,] x = new int[2,4];
	public static void Main() {
		for (int i = 0; i < 2; i++)
			for (int j = 0; j < 4; j++)
				x[i,j] = i+j;
		print(x);
	}
	static void print(System.Collections.IEnumerable x) {
		foreach (int i in x)
			System.Console.WriteLine(i);
	}
}

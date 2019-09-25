// using point = System.Drawing.Point;

struct point {
	int x,y;
	public point(int x, int y) { this.x = x; this.y = y; }
	override public string ToString() { return System.String.Format("({0},{1})", x, y); }
}

public class test {
	static point[,] x = new point[2,4];
	public static void Main() {
		for (int i = 0; i < 2; i++)
			for (int j = 0; j < 4; j++)
				x[i,j] = new point(i, j);
		print(x);
	}
	static void print(System.Collections.IEnumerable x) {
		foreach (point p in x)
			System.Console.WriteLine(p);
	}
}

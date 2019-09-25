using System;
using point = System.Drawing.Point;

public class test {
	public static void Main() {	(new test()).print(); }
	test() {
		for (int i = 0; i <= x.GetUpperBound(0); i++)
			for (int j = 0; j < x.GetUpperBound(1); j++)
				x[i,j] = new point(i, j);
	}
	void print() {
		foreach (point p in x)
			Console.WriteLine(p);
	}
	point[,] x = new point[4,4];
}

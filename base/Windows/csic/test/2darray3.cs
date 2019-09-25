using System;
public class test {
	struct box {
		public int x, y;
		public box(int x) { this.x = x; y = 0; }
		override public string ToString() {
			return String.Format("{0},{1}", x, y);
		}
	}
	static public void Main() {
		box[,] b = {{new box(10), new box(11)},
			{new box(12), new box(13)},
			{new box(14), new box(15)},
			{new box(16), new box(17)},
			{new box(18), new box(19)}};
		b[4,1].x = 20;
		Console.WriteLine("{0} {1}", b.GetUpperBound(0), b.GetUpperBound(1));
		for (int i = 0; i <= b.GetUpperBound(0); i++)
			for (int j = 0; j <= b.GetUpperBound(1); j++)
				Console.WriteLine(b[i,j]);
	}
}
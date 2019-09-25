using System;
class D {
	public const float B=((int)A.X)*3.0F;
	public const int C=3;
	public const A E=A.Y;
	public static void Main() {
		Console.WriteLine("B={0}", B);
		Console.WriteLine("C={0}", C);
		Console.WriteLine("D={0}={1}", E, (int)E);
	}
}
enum A { X=D.C, Y }

using System;
namespace N {
enum A {X=Y-1, Y=1, Z=X+2, W=B.X+3};
enum B {W=3, X};
public class Test {
	static A x = A.Z;
	public static void Main() {
		Console.WriteLine("{0}={1}", x, (int)x);
		Console.WriteLine("{0}={1}", A.W, (int)A.W);
	}
}
}


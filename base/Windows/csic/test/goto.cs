using System.Collections;
using System.Drawing;
public class A {
	public static void Main() {
		ArrayList x = new ArrayList();
		foreach (string a in x) {
			System.Console.WriteLine(a);
			goto done;
		}
done: System.Console.WriteLine("done");
		foreach (int a in x)
			;
		Point[] y = new Point[5];
		foreach (Point a in y)
			System.Console.WriteLine(a.X);
	}
}

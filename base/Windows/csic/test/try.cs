using System;
public class Test {
	static int x=3;
	public static int Main() {
		try {
			if (x>2)
				return(0);
			else if (x<0)
				return(1);
		}
		finally {
			Console.WriteLine("not so fast");
		}
		return(5);
	}
}

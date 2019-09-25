using System;
class test {
	static void F() {
		try {
			G();
		} catch (Exception e) {
			Console.WriteLine("Exception in F: " + e.Message);
			e = new Exception("F");
			//throw;		// re-throw
			throw e;	// throw a new exception
		} catch {
			;
		} finally {
			Console.WriteLine("F finally block");
		}
	}
	static void G() {
		throw new Exception("G");
	}
	public static void Main() {
		try {
			F();
		} catch (Exception e) {
			Console.WriteLine("Exception in Main: " + e.Message);
		}
	}
}
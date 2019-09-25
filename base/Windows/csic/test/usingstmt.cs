using System.IO;
struct P: System.IDisposable {
	public int x, y;
	public void Dispose() {}
	public P(int x) { this.x = x; this.y = 1; }
}
class T {
	static public void Main() {
		P a;
		a.x = 0; a.y = 1;
		while (true)
			using (P x = new P(), y = x) {
				if (x.x == y.x)
					break;
				goto x;
			}
		x: ;
		using (a) { ; }
	}
}

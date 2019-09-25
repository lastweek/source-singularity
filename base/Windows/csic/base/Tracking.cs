using System;
using System.IO;
using System.Collections;

public interface ITrackable {
	object subject { get; }
}

public class Tracking : TextWriter {
	public override System.Text.Encoding Encoding { get { return null; } }
	public class Pair {
		public int begin;
		public int end;
		public Pair(int begin, int end) {
			this.begin = begin;
			this.end = end;
		}
	}

	private System.Text.StringBuilder sb = new System.Text.StringBuilder();
	public string Text { get { return sb.ToString(); } }

	private int location = 0;
	public ITrackable tracked;
	public Tracking() {
	}

	public override void Write(char ch) {
		this.Track(tracked.subject, ch);
		sb.Append(ch);
		location = sb.Length;
	}

	public Hashtable table = new Hashtable();
	public void Track(object p, char ch) {
		if (p != null) {
			if (!table.Contains(p)) {
				ArrayList a = new ArrayList();
				table[p] = a;
				a.Add(new Pair(location, location+1));
			} else {
				ArrayList a = (ArrayList)table[p];
				Pair pair = (Pair)a[a.Count-1];
				if (pair.end == location) {
					pair.end = location+1;
				} else {
					a.Add(new Pair(location, location+1));
				}
			}
		}
	}

	private Hashtable Memo = new Hashtable();
	public Pair Span(object o) {
		if (!Memo.Contains(o)) {
			if (table.Contains(o)) {
				int lo = location;
				int hi = 0;
				foreach (Pair p in (ArrayList)table[o]) {
					if (p.begin < lo) lo = p.begin;
					if (p.end > hi)   hi = p.end;
				}
				Memo[o] = new Pair(lo, hi);
			} else {
				Memo[o] = null;
			}
		}
		return (Pair) Memo[o];
	}
}

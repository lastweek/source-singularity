using System;
using System.IO;
using System.Text;
using System.Reflection;
using System.Collections;
using System.Runtime.InteropServices;
using SHDocVw;

public interface IImage {
	string Image();
}

public class Debug {
	Debug() {}
	static public void Assert(bool cond) {
		System.Diagnostics.Debug.Assert(cond);
	}
	static public long Clock {
		get { return DateTime.Now.Ticks; }
	}
	static public void Report(string name, long time) {
		if (name.Length > 0)
			name += ": ";
		Console.Error.WriteLine("[{0}{1:f4}s]", name, time*100.0E-9);
	}
	static public void Fail(string msg) {
		System.Diagnostics.Debug.Fail(msg);
	}
	static public bool IsSystemObject(object o) {
		return o is Symbol && ((Symbol)o).FullName.StartsWith("System")
			|| o is SymbolTable && IsSystemObject(((SymbolTable)o).Owner);
	}
	static public bool IsLeafType(object o) {
		if (o == null)
			return true;
		System.Type t = o.GetType();
		return o is string || o is IImage || t.IsValueType || t.IsPrimitive
			|| o is ICollection && ((ICollection)o).Count == 0
			|| IsSystemObject(o);
	}
	static string Identity(object o, bool html) {
		if (o == null)
			return "null";
		if (o is IImage)
			return ((IImage)o).Image();
		else if (o is ICollection && ((ICollection)o).Count == 0)
			return String.Format("{0}#{1} (empty)", o.GetType().Name, o.GetHashCode());
		else if (IsLeafType(o))
			return o.ToString();
		else if (html)
			return String.Format("<a href=\"#{0}\">{1}</a>", o.GetHashCode(), Identity(o, false));
		else
			return String.Format("{0}#{1}", o.GetType().Name, o.GetHashCode());
	}
	static public string Identity(object o) {
		return Identity(o, false);
	}
	const BindingFlags bindingFlags = BindingFlags.Instance|BindingFlags.Public|BindingFlags.NonPublic;
	static public string Image(object o) {
		System.Type t = o.GetType();
		StringBuilder sb = new StringBuilder();
		sb.Append(t.Name);
		sb.Append('{');
		int i = 0;
		foreach (FieldInfo f in t.GetFields(bindingFlags)) {
			if (i++ > 0)
				sb.Append(',');
			sb.AppendFormat("{0}={1}", f.Name, Identity(f.GetValue(o)));
		}
		if (o is IDictionary)
			foreach (DictionaryEntry e in (IDictionary)o) {
				if (i++ > 0)
					sb.Append(',');
				sb.AppendFormat("[{0}]={1}", e.Key, e.Value);
			}
		else if (o is IEnumerable)
			foreach (object x in (IEnumerable)o) {
				if (i++ > 0)
					sb.Append(',');
				sb.AppendFormat("{0}", x);
			}
		sb.Append('}');
		return sb.ToString();		
	}
	static void Dump(object o, TextWriter w, Queue q, Hashtable marked, bool html) {
		if (IsLeafType(o)) {
			w.WriteLine("{0}", Identity(o));
			return;
		}
		if (marked != null) {
			if (marked.Contains(o))
				return;
			marked.Add(o, null);
		}
		if (html)
			w.WriteLine("<dt><a name=\"{1}\">{0}</a>:<dd>", Identity(o), o.GetHashCode());
		else
			w.WriteLine("{0}:", Identity(o));
		System.Type t = o.GetType();
		if (t.IsClass)
			foreach (FieldInfo f in t.GetFields(bindingFlags)) {
				object value = f.GetValue(o);
				w.WriteLine(html ? "{0}={1}<br>" : "\t{0}={1}", f.Name, Identity(value, html));
				if (q != null && !IsLeafType(value))
					q.Enqueue(value);
			}
		if (o is IDictionary)
			foreach (DictionaryEntry e in (IDictionary)o) {
				object value = e.Value;
				w.WriteLine(html ? "[{0}]={1}<br>" : "\t[{0}]={1}", Identity(e.Key), Identity(value, html));
				if (q != null && !IsLeafType(value))
					q.Enqueue(value);
			}
		else if (o is IEnumerable)
			foreach (object x in (IEnumerable)o) {
				w.WriteLine(html ? "{0}<br>" : "\t{0}", Identity(x, html));
				if (q != null && !IsLeafType(x))
					q.Enqueue(x);
			}
	}
	static public void Dump(object o, TextWriter w) { Dump(o, w, null, null, false); }
	static public void Dump(object o) { Dump(o, Console.Error, null, null, false); }
	static public void DumpAll(object o) { DumpAll(o, Console.Error, false); }
	class cmp: IComparer {
		public int Compare(object x, object y) {
			return Object.Equals(x,y) ? 0 : 1;
		}
	}
	static void DumpAll(object o, TextWriter w, bool html) {
		Hashtable marked = new Hashtable(null, new cmp());
		Queue worklist = new Queue();
		worklist.Enqueue(o);
		while (worklist.Count > 0)
			Dump(worklist.Dequeue(), w, worklist, marked, html);
	}
	static public void DumpAll(object o, TextWriter w) {
		DumpAll(o, w, false);
	}
	static public void DumpAllHTML(object o, TextWriter w) {
		w.WriteLine("<html><body><p><small>{0}</small></p><dl>", DateTime.Now.ToString());
		DumpAll(o, w, true);
		w.WriteLine("</dl><body><html>");
	}
}

public class display {
	public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
		int nf = 0;
		string oname = null;
		foreach (string s in args)
			if (s.StartsWith("-file=")) {
				oname = s.Substring(6);
				nf++;
			}
		if (oname == null) {
			oname = Path.GetTempFileName();
			File.Delete(oname);
			oname = Path.ChangeExtension(oname, ".htm");
		}
		try {
			TextWriter wr = new StreamWriter(oname);
			if (oname.EndsWith(".htm") || oname.EndsWith(".html"))
				Debug.DumpAllHTML(ast, wr);
			else
				Debug.DumpAll(ast, wr);
			wr.Close();
		} catch (Exception e) {
			msg.Error("can't write \"{0}\" ({1})", oname, e.ToString());
			return ast;
		}
		if (nf == 0) {
			try {
				object o = null;
				IWebBrowserApp ie = new SHDocVw.InternetExplorer();
				ie.Visible = true;
				ie.Navigate(oname, ref o, ref o, ref o, ref o);
			} catch (Exception e) {
				msg.Error("can't launch Internet Explorer ({0})", e.ToString());
			}
		}
		return ast;
	}
}

using System;

class tlist {
	public static void Main(string[] argv) {
		Console.WriteLine(
@"using System;
using System.Text;
using System.Collections;
using System.Reflection;"
		);
		foreach (string arg in argv) {
			string def = body;
			if (arg == "int" || arg == "string")
				def = Repl(def, "<Interfaces>", ", IImage") + body2;
			else
				def = Repl(def, "<Interfaces>", "");
			def = Repl(def, "<T>", arg);
			Console.WriteLine("{0}{1}", def, "}");
		}
	}
	static string Repl(string str, params string[] pairs) {
		for (int i = 0; i < pairs.Length; i += 2)
			str = str.Replace(pairs[i], pairs[i+1]);
		return str;
	}
	const string body = @"
public class <T>List : CollectionBase, IList<Interfaces> {

	// Constructors
	public <T>List() : base() {}
	public <T>List(ICollection c) : base() {
		foreach (<T> item in c)
			Add(item);
	}
	public <T>List(params <T>[] items) : this((ICollection)items) {}
	public static <T>List New(params <T>[] items) {
		return new <T>List(items);
	}		

	// Properties
	public <T> this[int index] {
		get { return (<T>)InnerList[index]; }
		set { InnerList[index] = value; }
	}

	// Methods
	public int Add(<T> value) {
		return InnerList.Add(value);
	}
	public void AddRange(ICollection c) {
		foreach (<T> x in c)
			Add(x);
	}
	public bool Contains(<T> value) {
		return InnerList.Contains(value);
	}
	public int IndexOf(<T> value) {
		return InnerList.IndexOf(value);
	}
	public void Insert(int index, <T> value) {
		InnerList.Insert(index, value);
	}
	public void Remove(<T> value) {
		InnerList.Remove(value);
	}
	public void Sort() {
		InnerList.Sort();
	}
	public int BinarySearch(<T> value) {
		return InnerList.BinarySearch(value);
	}
	class enumerator : IEnumerator {
		IEnumerator InnerEnumerator;
		public enumerator(IEnumerator InnerEnumerator) {
			this.InnerEnumerator = InnerEnumerator;
		}
		object IEnumerator.Current {
			get { return InnerEnumerator.Current; }
		}
		public <T> Current {
			get { return (<T>)InnerEnumerator.Current; }
		}
		public bool MoveNext() {
			return InnerEnumerator.MoveNext();
		}
		public void Reset() {
			InnerEnumerator.Reset();
		}
	}
	public new IEnumerator GetEnumerator() {
		return new enumerator(base.GetEnumerator());
	}
";
	const string body2 = @"
	// IImage
	string IImage.Image() {
		return Debug.Image(this);
	}
";
}
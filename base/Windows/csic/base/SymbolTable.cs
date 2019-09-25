using System;
using System.IO;
using System.Collections;

public class SymbolTable: DictionaryBase, IDictionary, IEnumerable {
	public Symbol Owner = null;

	// Constructors
	public SymbolTable(): base() {}
	public SymbolTable(Symbol owner) {
		this.Owner = owner;
	}

	// Properties
	public Symbol this[string key] {
		get { return (Symbol)InnerHashtable[key]; }
	}

	// IDictionary
	void IDictionary.Add(object key, object value) {
		Add((string)key, (Symbol)value);
	}
	void IDictionary.Clear() {
		InnerHashtable.Clear();
	}
	bool IDictionary.Contains(object key) {
		return Contains((string)key);
	}
	void IDictionary.Remove(object key) {
		Remove((string)key);
	}
	object IDictionary.this[object key] {
		get { return this[(string)key]; }
		set { throw new InvalidOperationException(); }
	}

	// Instance Methods
	public void Add(string key, Symbol value) {
		if (InnerHashtable.Contains(key))
			Debug.Fail(Owner.FullName + " already holds " + key);
		InnerHashtable.Add(key, value);
	}
	public bool Contains(string key) {
		return InnerHashtable.Contains(key);
	}
	public virtual void Dump(TextWriter w) {
		Debug.Dump(this, w);
	}
	public void Dump() {
		Dump(Console.Error);
	}
	public void Remove(string key) {
		InnerHashtable.Remove(key);
	}
	public override string ToString() {
		return String.Format("{0}#{1}", base.ToString(), GetHashCode());
	}

	// IEnumerable	
	class SymbolTableEnumerator: IDictionaryEnumerator, IEnumerator {
		IEnumerator InnerEnumerator;
		public SymbolTableEnumerator(IEnumerator inner) {
			InnerEnumerator = inner;
		}
		public object Current {
			get { return InnerEnumerator.Current; }
		}
		public DictionaryEntry Entry {
			get { return (DictionaryEntry)InnerEnumerator.Current; }
		}
		object IDictionaryEnumerator.Key {
			get { return Entry.Key; }
		}
		public string Key {
			get { return (string)Entry.Key; }
		}
		public bool MoveNext() {
			return InnerEnumerator.MoveNext();
		}
		object IDictionaryEnumerator.Value {
			get { return Entry.Value; }
		}
		public Symbol Value {
			get { return (Symbol)Entry.Value; }
		}
		public void Reset() {
			InnerEnumerator.Reset();
		}
	}
	IEnumerator IEnumerable.GetEnumerator() {
		return new SymbolTableEnumerator(InnerHashtable.GetEnumerator());
	}

}

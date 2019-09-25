abstract class InputFilterEnumerator : InputElementEnumerator {
	protected InputElementEnumerator iee;

	public InputFilterEnumerator(InputElementEnumerator iee) {
		this.iee = iee;
	}

	override public bool MoveNext() {
		for (;;) {
			if (!iee.MoveNext()) {
				return false;
			}
			if (predicate()) {
				return true;
			}
		}
	}

	override public InputElement Current {
		get {
			return iee.Current;
		}
	}

	abstract protected bool predicate();
}

class SkipWhiteEnumerator : InputFilterEnumerator {
	public SkipWhiteEnumerator(InputElementEnumerator iee) : base(iee) {
	}

	protected override bool predicate() {
		switch (iee.Current.tag) {
		case "WHITESPACE":
		case "NEWLINE":
		case "COMMENT":
			return false;
		}
		return true;
	}
}

public class EchoInputEnumerator : InputElementEnumerator {
	protected InputElementEnumerator iee;
	protected string prefix;

	public EchoInputEnumerator(InputElementEnumerator iee) {
		this.iee = iee;
		prefix = "";
	}

	public EchoInputEnumerator(InputElementEnumerator iee, string prefix) {
		this.iee = iee;
		this.prefix = prefix;
	}

	override public bool MoveNext() {
		if (iee.MoveNext()) {
			System.Console.WriteLine(prefix + "Token: " + iee.Current.tag + (iee.Current.tag != iee.Current.str ? "," + iee.Current.str : ""));
			return true;
		}
		return false;
	}

	override public InputElement Current {
		get {
			return iee.Current;
		}
	}
}

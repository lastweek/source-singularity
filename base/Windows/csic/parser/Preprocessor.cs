public abstract class AbstractPreprocessorEnumerator : InputElementEnumerator {
	protected bool Verbose = false;
	protected bool emitting;
	protected System.Collections.Hashtable table;
	protected InputElementEnumerator iee;
	protected AbstractPreprocessorEnumerator subordinate;

	protected int linedelta;
	protected string file;

	public AbstractPreprocessorEnumerator(InputElementEnumerator iee) {
		this.iee = iee;
		linedelta = 0;
	}

	public override InputElement Current {
		get {
			return iee.Current;
		}
	}

	public override bool MoveNext() {
		// System.Console.WriteLine("MoveNext[" + this.ToString() + "]");
		if (subordinate != null) {
			if (subordinate.MoveNext()) {
				return true;
			}
			subordinate = null;
		}
		return _moveNext();
	}

	protected abstract bool _moveNext();

	protected void tokenize(InputElement ie) {
		String2CharEnumerator s2ce = new String2CharEnumerator(ie.str);
		PreprocessorInputElementEnumerator pp = new PreprocessorInputElementEnumerator(s2ce, ie.coord.file);
		SkipWhiteEnumerator swe = new SkipWhiteEnumerator(pp);
		tokens = swe;
		if (Verbose) {
			tokens = new EchoInputEnumerator(tokens, "PPD> ");
		}
	}
	protected InputElementEnumerator tokens;

	protected void doLine() {
		if (!tokens.MoveNext()) {
			error("incomplete #line");
			return;
		}
		if (tokens.Current.tag != "integer-literal") {
			error("expecting integer");
			return;
		}
		string line = tokens.Current.str;
		if (emitting) {
			try {
				this.linedelta = System.Convert.ToInt32(line) - iee.Current.coord.line;
			} catch (System.OverflowException) {
				error("line number too big");
			}
		}
		if (!tokens.MoveNext()) {
			return;
		}
		if (tokens.Current.tag == "<EOF>") {
			return;
		}
		if (tokens.Current.tag != "string-literal") {
			error("expecting string");
		}
		file = tokens.Current.str;
	}

	protected void doWarning() {
		if (emitting) {
		}
	}

	protected void doError() {
		if (emitting) {
		}
	}

	protected void doDefine() {
		if (!tokens.MoveNext()) {
			error("incomplete #define");
			return;
		}
		if (tokens.Current.tag != "identifier") {
			error("expecting identifier");
			return;
		}
		if (emitting) {
			table.Add(tokens.Current.str, tokens.Current.str);
		}
	}
	protected void doPragma() {
		if (!tokens.MoveNext()) {
			error("incomplete #pragma");
			return;
		}

		if (tokens.Current.str != "warning") {
			error("expecting warning");
			return;
		}

        if (!tokens.MoveNext()) {
			error("incomplete #pragma");
			return;
		}

        switch (tokens.Current.str)
        {
            case "disable":
            case "restore":
                break;

            default :
                error("expecting disable or restore");
                return;
        
        }

        if (!tokens.MoveNext()) {
			error("incomplete #pragma");
			return;
		}
        // now we are at the error number
	}

    protected void doUndef() {
		if (!tokens.MoveNext()) {
			error("incomplete #undefine");
			return;
		}
		if (tokens.Current.tag != "identifier") {
			error("expecting identifier");
			return;
		}
		if (emitting) {
			table.Remove(tokens.Current.str);
		}
	}

	protected void error(string str) {
		System.Console.WriteLine("line " + iee.Current.coord.line + ": Preprocessor Error: " + str);
	}

	protected bool eval() {
		if (!tokens.MoveNext()) {
			error("incomplete expression");
			return true;
		}
		return e1();
	}

	bool e1() {
		bool v;
		v = e2();
		while (tokens.Current.tag == "||") {
			if (!tokens.MoveNext()) {
				error("incomplete expression");
				return true;
			}
			v |= e2();
		}
		return v;
	}

	bool e2() {
		bool v;
		v = e3();
		while (tokens.Current.tag == "&&") {
			if (!tokens.MoveNext()) {
				error("incomplete expression");
				return true;
			}
			v &= e3();
		}
		return v;
	}

	bool e3() {
		bool v;
		v = e4();
		for (;;) {
			switch (tokens.Current.tag) {
			case "==":
				if (!tokens.MoveNext()) {
					error("incomplete expression");
					return true;
				}
				v = (v == e4());
				break;
			case "!=":
				if (!tokens.MoveNext()) {
					error("incomplete expression");
					return true;
				}
				v = (v != e4());
				break;
			default:
				return v;
			}
		}
	}

	bool e4() {
		if (tokens.Current.tag == "!") {
			if (!tokens.MoveNext()) {
				error("incomplete expression");
				return true;
			}
			return !e4();
		}
		return e5();
	}

	bool e5() {
		bool v;
		switch (tokens.Current.tag) {
		case "true":
			return true;
		case "false":
			return false;
		case "(":
			if (!tokens.MoveNext()) {
				error("incomplete expression");
				return true;
			}
			v = e1();
			if (tokens.Current.tag != ")") {
				error("incomplete expression");
				return true;
			}
			if (!tokens.MoveNext()) {
				error("incomplete expression");
				return true;
			}
			return v;
		case "identifier":
			v = table.ContainsKey(tokens.Current.str);
			if (!tokens.MoveNext()) {
				error("incomplete expression");
				return true;
			}
			return v;
		}
		error("invalid expression");
		return true;
	}
}

public class PreprocessorEnumerator : AbstractPreprocessorEnumerator {

	public PreprocessorEnumerator(InputElementEnumerator iee) : base(iee) {
		this.table = new System.Collections.Hashtable();
		this.emitting = true;
	}

	public PreprocessorEnumerator(InputElementEnumerator iee, bool Verbose) : this(iee) {
		this.Verbose = Verbose;
	}

	protected override bool _moveNext() {
		System.Diagnostics.Trace.Assert(emitting);
		while (iee.MoveNext()) {
			if (iee.Current.tag != "PREPROC") {
				iee.Current.coord.line += linedelta;
				if (file != null) {
					iee.Current.coord.file = file;
				}
				return true;
			}
			tokenize(iee.Current);
			bool status = tokens.MoveNext();
			switch (tokens.Current.tag) {
			default:
				error("unknown preprocessor command: " + tokens.Current.tag);
				break;
			case "define":
				doDefine();
				break;
			case "undef":
				doUndef();
				break;
			case "line":
				doLine();
				break;
			case "error":
				doError();
				break;
			case "warning":
				doWarning();
				break;
			case "region":
				subordinate = new RegionEnumerator(table, iee, emitting);
				if (subordinate.MoveNext()) {
					return true;
				}
				subordinate = null;
				continue;
			case "endregion":
				error("unexpected #endregion");
				break;
            case "pragma":
				doPragma();
                break;
			case "if":
				bool val = eval();
				subordinate = new IfEnumerator(table, iee, emitting, val);
				if (subordinate.MoveNext()) {
					return true;
				}
				subordinate = null;
				continue;
			case "elif":
				error("unexpected #elif");
				break;
			case "else":
				error("unexpected #else");
				break;
			case "endif":
				error("unexpected #endif");
				break;
			}
		}
		return false;
	}
}

public class RegionEnumerator : AbstractPreprocessorEnumerator {

	public RegionEnumerator(System.Collections.Hashtable table, InputElementEnumerator iee, bool emitting) : base(iee) {
		this.table = table;
		this.emitting = emitting;
	}

	protected override bool _moveNext() {
		while (iee.MoveNext()) {
			if (iee.Current.tag != "PREPROC") {
				if (emitting) {
					iee.Current.coord.line += linedelta;
					if (file != null) {
						iee.Current.coord.file = file;
					}
					return true;
				}
				continue;
			}
			tokenize(iee.Current);

			bool status = tokens.MoveNext();
			switch (tokens.Current.tag) {
			default:
				error("unknown preprocessor command: " + tokens.Current.tag);
				break;
			case "define":
				doDefine();
				break;
			case "undef":
				doUndef();
				break;
			case "line":
				doLine();
				break;
			case "error":
				doError();
				break;
			case "warning":
				doWarning();
				break;
			case "region":
				subordinate = new RegionEnumerator(table, iee, emitting);
				if (subordinate.MoveNext()) {
					return true;
				}
				subordinate = null;
				continue;
			case "endregion":
				return false;
            case "pragma":
				doPragma();
                break;
			case "if":
				bool val = eval();
				subordinate = new IfEnumerator(table, iee, emitting, val);
				if (subordinate.MoveNext()) {
					return true;
				}
				subordinate = null;
				continue;
			case "elif":
				error("unexpected #elif");
				break;
			case "else":
				error("unexpected #else");
				break;
			case "endif":
				error("unexpected #endif");
				break;
			}
		}
		error("unfinished #region");
		return false;
	}
}

public class IfEnumerator : AbstractPreprocessorEnumerator {

	public IfEnumerator(System.Collections.Hashtable table, InputElementEnumerator iee, bool emitting, bool conditional) : base(iee) {

		this.table = table;
		this.emitting = emitting;
		if (emitting) {
			this.conditional = conditional;
			this.condHistory = conditional;
		} else {
			this.conditional = false;
			this.condHistory = true;
		}
	}

	private bool conditional;
	private bool condHistory;

	protected override bool _moveNext() {
		while (iee.MoveNext()) {
			bool val;

			if (iee.Current.tag != "PREPROC") {
				if (conditional) {
					iee.Current.coord.line += linedelta;
					if (file != null) {
						iee.Current.coord.file = file;
					}
					return true;
				}
				continue;
			}
			tokenize(iee.Current);

			bool status = tokens.MoveNext();
			switch (tokens.Current.tag) {
			default:
				error("unknown preprocessor command: " + tokens.Current.tag);
				break;
			case "define":
				doDefine();
				break;
			case "undef":
				doUndef();
				break;
			case "line":
				doLine();
				break;
			case "error":
				doError();
				break;
			case "warning":
				doWarning();
				break;
			case "region":
				subordinate = new RegionEnumerator(table, iee, emitting && conditional);
				if (subordinate.MoveNext()) {
					return true;
				}
				subordinate = null;
				continue;
			case "endregion":
				error("unexpected #endregion");
				break;
            case "pragma":
				doPragma();
                break;
			case "if":
				val = eval();
				subordinate = new IfEnumerator(table, iee, emitting && conditional, val);
				if (subordinate.MoveNext()) {
					return true;
				}
				subordinate = null;
				continue;
			case "elif":
				val = eval();
				conditional = val && !condHistory;
				condHistory |= conditional;
				break;
			case "else":
				conditional = !condHistory;
				condHistory = true;
				continue;
			case "endif":
				return false;
			}
		}
		error("unfinished #if");
		return false;
	}
}

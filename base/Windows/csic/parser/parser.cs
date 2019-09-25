public class Parser {
	InputElementEnumerator yylex;

	System.Collections.Queue wl;
	System.Collections.Queue wl_next;

	public Parser(InputElementEnumerator yylex) {
		this.yylex = yylex;

		yylex.MoveNext();

		wl = new System.Collections.Queue();
		wl.Enqueue(new startState());
		wl_next = new System.Collections.Queue();
	}

	int count = 0;

	public nonterminalState parse(System.IO.TextWriter err) {
		nonterminalState _current = null;
		InputElement cur = yylex.Current;
		InputElement prev = null;
		while (wl.Count > 0) {
			foreach (state s in wl) {
				s.end = cur.coord;
			}
			while (wl.Count > 0) {
				state s = (state) wl.Dequeue();

				if (s.below != null && s.below.checkRejected()) continue;

				if (s.accepting) {
					System.Diagnostics.Debug.Assert(_current == null);
					_current = ((acceptingState) s).root;
				} else {
					s.transitions(wl_next, cur, count);
				}
			}
			if (yylex.MoveNext()) {
				count++;
				prev = cur;
				cur = yylex.Current;
			}

			System.Collections.Queue tmp = wl;
			wl = wl_next;
			wl_next = tmp;
		}
		if (_current == null) {
			err.WriteLine("\"" + prev.coord.file + "\" (" + prev.coord.line + "," + prev.coord.column + "): Syntax error on \"" + prev.str + "\"");
		}
		return _current;
	}

	public static object parse(string filename, System.IO.TextReader r) {
		return parse(filename, r, false);
	}

	public static object parse(string filename, System.IO.TextReader r, bool Verbose) {
		CharEnumerator ce = new File2CharEnumerator(r);
		InputElementEnumerator iee = new Char2InputElementEnumerator(ce, filename);
		if (Verbose)
			iee = new EchoInputEnumerator(iee, "raw> ");
		iee = new PreprocessorEnumerator(iee);
		iee = new SkipWhiteEnumerator(iee);
		if (Verbose)
			iee = new EchoInputEnumerator(iee, "ppd> ");

		Parser p = new Parser(iee);
		nonterminalState parse = p.parse(System.Console.Error);
		if (parse != null) {
			if (Verbose) {
				System.Console.WriteLine("DERIVATION:");
				System.Console.WriteLine(parse.ToString(""));
			}
			object ast = parse.rewrite2AST();
			return ast;
		} else
			return null;
	}

	public static int Main(string[] argv) {
		try {
			return _main(argv);
		} catch (System.Exception e) {
			System.Console.WriteLine("ERROR: unhandled exception " + e.ToString());
			return 2;
		}
	}

	static int _main(string[] argv) {
		bool Verbose = false;
		if (argv.Length == 0 || argv[0] == "-verbose" && argv.Length == 1) {
			System.Console.Error.WriteLine("usage: parser [ -verbose ] file");
			return 2;
		}
		string filename;
		if (argv[0] == "-verbose") {
			Verbose = true;
			filename = argv[1];
		} else
			filename = argv[0];
		System.IO.TextReader r;
		try {
			r = new System.IO.StreamReader(filename);
		} catch {
			System.Console.Error.WriteLine("parser: can't read \"{0}\"", filename);
			return 2;
		}
		object ast = parse(filename, r, Verbose);
		r.Close();
		if (ast == null) {
			System.Console.Error.WriteLine("no parse");
			return 1;
		}
		return 0;
	}
}

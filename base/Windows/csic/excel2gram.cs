using System;
using System.Collections;

public class excel2gram {
	public static void Main(string[] argv) {
		string command = argv[0];

		ArrayList filenames = new ArrayList();
		for (int i = 1; i < argv.Length; i++) {
			string excelname = argv[i];

			if (!System.IO.Path.IsPathRooted(excelname)) {
				string cwd = System.Environment.CurrentDirectory;
				excelname = System.IO.Path.Combine(cwd, excelname);
			}

			filenames.Add(excelname);
		}

		Excel.Application app = new Excel.Application();
		doit(app, filenames, command);
		app.Quit();
	}

	public static void doit(Excel.Application app, ArrayList excelnames, string command) {
		ArrayList prods = new ArrayList();
		ArrayList words = new ArrayList();
		Hashtable nts = new Hashtable();

		foreach (string excelname in excelnames) {
			Excel.Workbook wb = app.Workbooks.Open(
				excelname,			// Filename
				0,				// UpdateLinks
				true,				// ReadOnly
				5,				// Format
				"",				// Password
				"",				// WriteResPassword
				true,				// IgnoreReadOnlyRecommended
				Excel.XlPlatform.xlWindows,	// Origin
				"\t",				// Delimiter
				false,				// Editable
				false,				// Notify
				0,				// Converter
				true,				// AddToMru
				true,				// Local
				true				// CorruptLoad
				);

			prods = process(wb, prods);
			nts = processTypes(wb, nts);
			words = processKeyword(wb, words);
		}

		switch (command) {
		default:
			System.Console.WriteLine("usage: a.out (grammar|keywords) excelfile");
			break;
		case "gram":
			prods = addOpts(prods, nts);
			foreach (production p in prods) {
				System.Console.WriteLine(p.prod);
			}
			break;
		case "rewrite":
			prods = addOpts(prods, nts);
			emitParse2AST(nts, prods);
			break;
		case "keywords":
			foreach (string s in words) {
				System.Console.WriteLine(s);
			}
			break;
		}
	}


	class production {
		public string nt;
		public IList rule;
		public string ty;
		public string action;
		public production(string nt, IList rule, string ty, string action) {
			this.nt = nt;
			this.rule = rule;
			this.ty = ty;
			this.action = action;
		}
		public override string ToString() {
			return prod + " = " + ty + " " + action;
		}

		public string prod {
			get {
				string s = nt + " :";
				foreach (string e in rule) {
					s += " " + e;
				}
				return s;
			}
		}
	}

	static ArrayList addOpts(ArrayList prods, Hashtable nts) {
		ArrayList L = new ArrayList();
		foreach (production p in prods) {
			L.Add(p);
		}
		foreach (production p in prods) {
			foreach (string s in p.rule) {
				if (s.EndsWith("opt") && !nts.Contains(s)) {
					string basename = s.Substring(0, s.LastIndexOf("opt"));
					production q;
					string ty;
					if (nts.Contains(basename)) {
						ty = ((typeInfo)nts[basename]).ty;
						string action = ((typeInfo)nts[basename]).action;
						q = new production(s, new string[] {}, ty, action);
						L.Add(q);
						q = new production(s, new string[] { basename }, ty, "a1");
						L.Add(q);
						nts[s] = new typeInfo(ty, "");
					} else {
						ty = "InputElement";
						q = new production(s, new string[] {}, ty, "null");
						L.Add(q);
						q = new production(s, new string[] { basename }, ty, "a1");
						L.Add(q);
					}
					nts[s] = new typeInfo(ty, "");
				}
			}
		}
		return L;
	}

	static ArrayList process(Excel.Workbook wb, ArrayList prods) {
		foreach (Excel.Worksheet ws in wb.Sheets) {
			if (ws.Name.EndsWith("grammar")) {
				Excel.Range nonterms = ws.get_Range("grammar_Nonterminal",missing);
				Excel.Range rules = ws.get_Range("grammar_Rule",missing);
				Excel.Range types = ws.get_Range("grammar_type",missing);
				Excel.Range actions = ws.get_Range("grammar_Action",missing);
				for (int i = 1; i <= ws.UsedRange.Rows.Count; i++) {
					string nt = item(nonterms, i);
					string rule = item(rules, i);
					string ty = item(types, i);
					string action = item(actions, i);
					if (action == "") {
						if (rule == "") {
							action = "null";
						} else {
							action = "a1";
						}
					}
					if (nt != "") {
						string[] rx = rule.Trim(' ').Split(' ');
						production p = new production(nt, rx, ty, action);
						prods.Add(p);
					}
				}
			}
		}
		return prods;
	}

	class typeInfo {
		public string ty;
		public string action;
		public typeInfo(string ty, string action) {
			this.ty = ty;
			this.action = action;
		}
	}

	static Hashtable processTypes(Excel.Workbook wb, Hashtable T) {
		foreach (Excel.Worksheet ws in wb.Sheets) {
			if (ws.Name.EndsWith("types")) {
				Excel.Range nonterms = ws.get_Range("types_Nonterminal",missing);
				Excel.Range types = ws.get_Range("types_type",missing);
				Excel.Range actions = ws.get_Range("types_Default_Action",missing);
				for (int i = 1; i <= ws.UsedRange.Rows.Count; i++) {
					string nt = item(nonterms, i);
					string ty = item(types, i);
					string action = item(actions, i);
					if (nt != "") {
						T[nt] = new typeInfo(ty, action);
					}
				}
			}
		}
		return T;
	}

	static object missing = System.Reflection.Missing.Value;

	static string item(Excel.Range r, int row) {
		Excel.Range c;
		try {
			c = r.get_Range("A"+row, missing);
		} catch (System.Exception e) {
			System.Console.WriteLine("error: {0} --- {1}", row, e);
			throw e;
		}
		if (c.Value2 == null) {
			return "";
		}
		return c.Value2.ToString();
	}

	static string item(Excel.Worksheet ws, string column, int row) {
		Excel.Range c;
		try {
			c = ws.get_Range(column,missing).get_Range("A"+row, missing);
		} catch (System.Exception e) {
			System.Console.WriteLine("error: {0}.{1}[{2}] --- {3}", ws.Name, column, row, e);
			throw e;
		}
		if (c.Value2 == null) {
			return "";
		}
		return c.Value2.ToString();
	}

	static ArrayList processKeyword(Excel.Workbook wb, ArrayList words) {
		foreach (Excel.Worksheet ws in wb.Sheets) {
			if (ws.Name.EndsWith("keyword-tokens")) {
				Excel.Range keywords = ws.get_Range("tokens_Terminal",missing);
				for (int i = 1; i <= ws.UsedRange.Rows.Count; i++) {
					string token = item(keywords, i);
					if (token != "") {
						words.Add(token);
					}
				}
			}
		}
		return words;
	}


	private static Hashtable memo = new Hashtable();
	static string mangle(string name) {
		if (memo.Contains(name)) {
			return (string)memo[name];
		}
		string s = name	.Replace('-', '_')
				.Replace(';', 'A');
		memo[name] = s;
		return s;
	}

	static void emitParse2AST(Hashtable nts, IList prods) {
		string prefix = "rewrite_";

		Console.WriteLine(@"
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//
// Generated Files --- DO NOT EDIT!
//
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

using System.Collections;

public class parse2AST {
");
		foreach (string nt in nts.Keys) {
			string ty = ((typeInfo)nts[nt]).ty;

			Console.WriteLine(@"
public static {0} {1}{2}(nonterminalState node) {{
	if (node.queue != null) {{
		return ({0})disambiguate.resolve(node, ""{3}"");
	}}
	{0} retval;
	switch (node.rule) {{
	default: throw new System.Exception(""{3}"");
", ty, prefix, mangle(nt), nt);
			
			foreach (production p in prods) {
				if (p.nt == nt) {
					Console.WriteLine("\tcase \"{0}\": {{", p.prod);
					if (p.rule.Count > 0) {
						Console.WriteLine("\t\tstate tmp = node.rightmost;");
					}
					for (int i = p.rule.Count-1; i >= 0; i--) {
						string sym = (string)p.rule[i];

						if (nts.Contains(sym)) {
							string symty = ((typeInfo)nts[sym]).ty;
Console.WriteLine("\t\t{0} a{1} = {2}{3}((nonterminalState)tmp);;", symty, i+1, prefix, mangle(sym));
						} else {
Console.WriteLine("\t\tInputElement a{0} = {1}terminal(tmp);", i+1, prefix);
						}
						if (i > 0) {
							Console.WriteLine("\t\ttmp = tmp.below;");
						}
					}

					Console.WriteLine(@"
		retval = {0};
		break;
		}}
", p.action);
				}

			}

			Console.WriteLine(@"
	}
	IHasCoordinate ihc = ((object)retval) as IHasCoordinate;
	if (ihc != null) {
		ihc.begin = node.begin;
		ihc.end = node.end;
	}
	return retval;
}
");

		}

		Console.WriteLine(@"
public static InputElement {0}terminal(state node) {{
	return ((terminalState)node).terminal;
}}
}}
", prefix);
	}
}

public class disambiguate {
	public static object resolve(nonterminalState node, string nonterm) {
		System.Collections.Queue q;
		expression e1;
		expression e2;

		switch (nonterm) {
		default:
			if (node.queue != null) {
				node.report();
				//System.Console.WriteLine("{0}", node.ToString(""));
				throw new System.Exception("ambiguous");
			}
			node.report();
			return null;
		case "argument-list":
			q = node.queue;
			node.queue = null;
			argumentList a = (argumentList)parse2AST.rewrite_argument_list(node);
			foreach (nonterminalState s in q) {
				argumentList a2 = (argumentList)parse2AST.rewrite_argument_list(s);
				if (a2.Count < a.Count)
					a = a2;
			}
			return a;
		case "relational-expression":
			q = node.queue;
			node.queue = null;
			e1 = parse2AST.rewrite_relational_expression(node);
			int n = TypeArgumentCount(e1);
			foreach (nonterminalState s in q) {
				e2 = parse2AST.rewrite_relational_expression(s);
				int m = TypeArgumentCount(e2);
				if (m > n) {
					n = m;
					e1 = e2;
				}
			}
			return e1;
		case "if-statement":
			q = node.queue;
			node.queue = null;
			// by picking the short production
			int count = 0;
			for (state p = node.rightmost; p != node.below; p = p.below) count++;
			bool ties = false;

			foreach (nonterminalState node1 in q) {
				int c = 0;
				for (state p = node1.rightmost; p != node1.below; p = p.below) c++;
				if (c < count) {
					node = node1;
					ties = false;
					count = c;
				} else if (c == count) {
					ties = true;
				}
			}

			System.Diagnostics.Debug.Assert(!ties);
			return parse2AST.rewrite_if_statement(node);

		case "and-expression":		// (e1) & e2 ambiguity
			q = node.queue;
			node.queue = null;
			e1 = parse2AST.rewrite_and_expression(node);
			System.Diagnostics.Debug.Assert(q.Count == 1);
			e2 = parse2AST.rewrite_and_expression((nonterminalState) q.Dequeue());
			return fix_cast(e1,e2);
		case "additive-expression":		// (e1) + e2 ambiguity
			q = node.queue;
			node.queue = null;
			e1 = parse2AST.rewrite_additive_expression(node);
			System.Diagnostics.Debug.Assert(q.Count == 1);
			e2 = parse2AST.rewrite_additive_expression((nonterminalState) q.Dequeue());
			return fix_cast(e1,e2);
		case "unary-expression":		//
			q = node.queue;
			node.queue = null;
			e1 = parse2AST.rewrite_unary_expression(node);
			System.Diagnostics.Debug.Assert(q.Count == 1);
			e2 = parse2AST.rewrite_unary_expression((nonterminalState) q.Dequeue());
			return fix_cast(e1,e2);
		case "multiplicative-expression":		// (e1) * e2 ambiguity
			q = node.queue;
			node.queue = null;
			e1 = parse2AST.rewrite_multiplicative_expression(node);
			System.Diagnostics.Debug.Assert(q.Count == 1);
			e2 = parse2AST.rewrite_multiplicative_expression((nonterminalState) q.Dequeue());
			return fix_cast(e1,e2);
		}
	}

	static expression fix_cast(expression e1, expression e2) {
		// the first two cases are simple optimizations for the common case.
		if (e1 is cast_expression) {
			if (e2 is invocation_expression) {
				return e1;
			}
			return e2;
		} else if (e2 is cast_expression) {
			if (e1 is invocation_expression) {
				return e2;
			}
			return e1;
		} else {
			//
			// This is to handle the pathological case of (a+(b)-c)
			// or worse, ((a+b)+c-(d)e)
			//
			// The code is complicated because neither parse is rooted with a cast...
			//
			CastCounter c1 = new CastCounter();
			ASTVisitor a1 = new ASTVisitor(c1.fn);
			e1.visit(a1);

			CastCounter c2 = new CastCounter();
			ASTVisitor a2 = new ASTVisitor(c2.fn);
			e2.visit(a2);

			if (c1.Count == c2.Count+1) {
				return e1;
			} else if (c1.Count == c2.Count-1) {
				return e2;
			} else {
				// fall off into error message.
			}
		}
		throw new System.Exception("failed to disambiguate expressions");
	}
	static int TypeArgumentCount(expression ast) {
		ArgumentCounter c = new ArgumentCounter();
		ASTVisitor v = new ASTVisitor(c.fn);
		ast.visit(v);
		return c.Count;
	}
}

class ArgumentCounter {
	int _count = 0;
	public int Count { get { return _count; } }
	public void fn(AST ast) {
		if (ast is simple_name && ((simple_name)(ast)).typeargs != null)
			_count += ((simple_name)(ast)).typeargs.Count;
		else if (ast is member_access && ((member_access)(ast)).typeargs != null)
			_count += ((member_access)(ast)).typeargs.Count;
	}
}

class CastCounter {
	int _count = 0;
	public int Count { get { return _count; } }

	public void fn(AST ast) {
		if (ast is cast_expression) {
			_count++;
		}
	}
}

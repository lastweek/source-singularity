public abstract class state {
	public state below;
	protected int serial;
	public bool rejected = false;

	public Coordinate begin;
	public Coordinate end;

	abstract public string ToString(string indent);

	public state() {}

	protected state(state below, int serial) {
		System.Diagnostics.Debug.Assert(this != below);
		System.Diagnostics.Debug.Assert(serial >= 0);
		this.below = below;
		this.serial = serial;
		if (below != null) {
			this.begin = below.end;
		}
	}

	abstract public bool checkRejected();

	private object cachedAST;
	private bool cached = false;
	public object rewrite2AST() {
		if (!cached) {
			cached = true;
			cachedAST = _rewrite2AST();
			IHasCoordinate ihc = cachedAST as IHasCoordinate;
			if (ihc != null) {
				ihc.begin = begin;
				ihc.end = end;
			}
		}
		return cachedAST;
	}
	abstract public object _rewrite2AST();

	public virtual bool accepting { get { return false; } }

	abstract public void transitions(System.Collections.Queue wl, InputElement tok, int count);
	public virtual state shiftNonterm(string nonterm, int count, Coordinate end, string rule, state rightmost) {
		throw new System.Exception(nonterm+"== "+rule);
	}
}

public abstract class acceptingState : nonterminalState {
	public nonterminalState root;

	public acceptingState() {}

	protected acceptingState(state below, string rule, state rightmost, Coordinate end, bool rejected, int serial) : base(below, rule, rightmost, end, false, serial) {
		System.Diagnostics.Debug.Assert(!rejected);
		this.root = (nonterminalState) rightmost;
	}

	public override string ToString(string indent) {
		return root.ToString(indent);
	}

	public override bool accepting { get { return true; } }
}

public abstract class nonterminalState : state {
	public state rightmost;
	public string rule;
	public System.Collections.Queue queue;

	public void report() {
		if (queue != null) {
			System.Console.WriteLine("AMBIGUITY:");
			System.Console.WriteLine("> " + this.rule);
			foreach (nonterminalState s in queue) {
				System.Console.WriteLine("> " + s.rule);
			}
		}
	}

	public override bool checkRejected() {
		if (this.rejected) return true;
		if (this.rightmost == null) return false;
		this.rejected = this.rightmost.checkRejected();
		int total = 1;
		int numrejected = this.rejected ? 1 : 0;

		if (this.queue != null) {
			foreach (nonterminalState nt in queue) {
				bool tmp = nt.checkRejected();
				total += 1;
				numrejected += tmp ? 1 : 0;
			}
		}
		if (numrejected == 0) return false;
		if (numrejected == total) {
			this.queue = null;
			return true;
		}
		// at least one, but not all, rejected
		System.Diagnostics.Debug.Assert(queue != null);
		if (total - numrejected == 1) {
			if (this.rejected) {
				foreach (nonterminalState nt in this.queue) {
					if (!nt.rejected) {
						this.rule = nt.rule;
						this.rejected = nt.rejected;
						this.rightmost = this.rightmost;
						break;
					}
				}
			}
			this.queue = null;
		} else {
			System.Diagnostics.Debug.Assert(total - numrejected > 1);
			System.Collections.Queue tmp = new System.Collections.Queue();
			foreach (nonterminalState nt in this.queue) {
				if (!nt.rejected) {
					if (this.rejected) {
						this.rule = nt.rule;
						this.rejected = nt.rejected;
						this.rightmost = this.rightmost;
					} else {
						tmp.Enqueue(nt);
					}
				}
			}
			this.queue = tmp;
		}
		return false;
	}

	public virtual void add(nonterminalState state, int count) {
		if (!this.rejected) {
			if (state.rejected) {
				this.rejected = state.rejected;	// true;
				this.rightmost = state.rightmost;
				this.rule = state.rule;
				this.queue = null;
			} else {
				if (queue == null) {
					queue = new System.Collections.Queue();
				}
				queue.Enqueue(state);
			}
		}
	}

	public nonterminalState() {}

	protected nonterminalState(state below, string rule, state rightmost, Coordinate end, bool rejected, int serial) : base(below, serial) {
		this.rejected = rejected;
		this.rightmost = rightmost;
		this.rule = rule;
		this.end = end;
	}

	public override string ToString(string indent) {
		string s = indent
		+ "<" + begin.ToString() + "-->" + end.ToString() + ">"
		+ " RULE: "
		+ rule + "\n";
		// string s = indent + "RULE: " + rule + "\n";
		string tmp = "";
		for (state p = rightmost; p != below; p = p.below) {
			tmp = p.ToString(indent+". ") + tmp;
		}
		s += tmp;
		if (queue != null) {
			foreach (nonterminalState nt in queue) {
				s += indent + "ALTERNATE:\n";
				s += nt.ToString(indent);
			}
		}
		return s;
	}
}


public abstract class terminalState : state {
	public InputElement terminal;

	public terminalState() {}

	protected terminalState(state below, InputElement terminal, int serial) : base(below, serial) {
		this.terminal = terminal;
	}

	public override bool checkRejected() {
		// System.Diagnostics.Debug.Assert(this.below != null);
		// if (this.rejected) return true;
		// this.rejected = this.below.checkRejected();
		// return this.rejected;
		return false;
	}

	public override string ToString(string indent) {
		return indent + terminal.tag + "\n";
	}

}

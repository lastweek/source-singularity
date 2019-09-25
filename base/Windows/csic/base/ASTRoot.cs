using System;
using System.Collections;

public delegate void ASTVisitor(AST ast);

public interface IHasCoordinate {
	Coordinate begin { get; set; }
	Coordinate end { get; set; }
}

abstract public class AST : IHasCoordinate, ICloneable {
	object ICloneable.Clone() { return MemberwiseClone(); }
	public AST Clone() { return (AST)((ICloneable)this).Clone(); }
	public static void donothing(AST ast) { }
	public static ASTVisitor postfix = new ASTVisitor(donothing);
	public static ASTVisitor prefix  = new ASTVisitor(donothing);
	public virtual void visit(ASTVisitor map) {
		visit(map, postfix);
	}
	public virtual void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		postfix(this);
	}
	class closure {
		public Stack stack = new Stack();
		public closure(AST parent) { stack.Push(parent); }
		public void prefix(AST ast) {
			ast.parent = (AST)stack.Peek();
			stack.Push(ast);
		}
		public void postfix(AST ast) {
			stack.Pop();
		}
	}
	public void link(AST parent) {
		closure c = new closure(parent);
		this.visit(new ASTVisitor(c.prefix), new ASTVisitor(c.postfix));
		Debug.Assert(c.stack.Count == 1);
	}
	private Coordinate _begin, _end;
	public virtual Coordinate begin {
		get { return _begin; }
		set { _begin = value; }
	}
	public virtual Coordinate end {
		get { return _end; }
		set { _end = value; }
	}
	public AST parent;
	public AST find(string name) {
		return find(System.Type.GetType(name));
	}
	public AST find(System.Type type) {
		AST t = this;
		while (t != null && t.GetType() != type)
			t = t.parent;
		return t;
	}
	public static AST leastCommonAncestor(AST u, AST v) {
		ASTList nodes = new ASTList();
		for ( ; u != null; u = u.parent)
			nodes.Add(u);
		for ( ; v != null; v = v.parent)
			if (nodes.Contains(v))
				return v;
		return null;
	}

	private class findHelper {
		private Coordinate begin;
		private Coordinate end;
		public AST ast;
		public findHelper(Coordinate begin, Coordinate end) {
			this.begin = begin;
			this.end = end;
		}
		public void fn(AST ast) {
			if (
				(ast.begin.originalFile == begin.originalFile) &&
				(ast.begin.fileOffset <= begin.fileOffset) &&
				(ast.end.fileOffset >= end.fileOffset)
			) {
				this.ast = ast;
			}
		}
	}

	public AST find(Coordinate begin, Coordinate end) {
		findHelper o = new findHelper(begin, end);
		ASTVisitor dele = new ASTVisitor(o.fn);
		this.visit(dele);
		return o.ast;
	}
}

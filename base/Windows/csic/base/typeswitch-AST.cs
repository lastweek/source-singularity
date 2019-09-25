using System;
using System.Collections;
using System.IO;
using System.Diagnostics;

public class typeswitch_label: switch_label {
	public type typelabel;
	public typeswitch_label(type typelabel) {
		this.typelabel = typelabel;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		typelabel.visit(prefix, postfix);
		postfix(this);
	}
}

public class typeswitch_section: AST {
	[MayBeNull] public InputElement id;
	public switch_labelList labels;
	public statementList stmts;
	public typeswitch_section(IList labels, IList stmts) {
		this.labels = (switch_labelList)labels;
		this.id = null;
		this.stmts = (statementList)stmts;
	}
	public typeswitch_section(type typelabel, InputElement id, IList stmts) {
		this.labels = switch_labelList.New(new typeswitch_label(typelabel));
		this.id = id;
		this.stmts = (statementList)stmts;
	}
	public typeswitch_section(IList stmts) {
		this.labels = switch_labelList.New(new switch_default());
		this.id = null;
		this.stmts = (statementList)stmts;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(labels, prefix, postfix);
		List.visit(stmts, prefix, postfix);
		postfix(this);
	}
	[Bind1] public Block block;		// bind: block for local id
	[MayBeNull,Bind2] public Local sym;	// bind: symbol-table entry for id
}

public class typeswitch_statement: statement {
	public expression expr;
	public typeswitch_sectionList sections;
	public typeswitch_statement(expression expr, IList sections) {
		this.expr = expr;
		this.sections = (typeswitch_sectionList)sections;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		List.visit(sections, prefix, postfix);
		postfix(this);
	}
	public int var;	// ilgen: temporary
}

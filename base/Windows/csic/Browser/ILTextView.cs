using System;
using System.Collections;
using System.Windows.Forms;

namespace Browser {
	public class ILTextView {
		public string Text { set { rtb.Text = value; } }
		public AST ASTRoot;
		Tracking tracking;

		private TextBox rtb;
		private Model model;
		public ILTextView(Model model, TextBox rtb) {
			this.model = model;
			this.rtb = rtb;
			model.ObjectChangedHandler += new ObjectChangedEventHandler(this.ObjectChanged);
			this.ObjectChanged();
		}

		public static Control NewControl(Model model, object o) {
			IHasCoordinate ihc = (IHasCoordinate) o;
			TextBox rtb = new TextBox();
			rtb.Multiline = true;
			rtb.ScrollBars = ScrollBars.Both;
			rtb.WordWrap = false;
			rtb.HideSelection = false;
			ILTextView stv = new ILTextView(model, rtb);
			if (ihc is AST) {
				AST p = (AST) ihc;
				while (p.parent != null && p.parent.begin.file == ihc.begin.file && !(p is compilation_unit)) {
					p = p.parent;
				}
				stv.ASTRoot = p;
				if (stv.ASTRoot is compilation_unit) {
					compilation_unit c = (compilation_unit) stv.ASTRoot;
					Tracking tracking = new Tracking();
					tracking_ilgen ti = new tracking_ilgen(tracking, c);
					tracking.tracked = ti;
					stv.tracking = ti.create(c);
					stv.Text = stv.tracking.Text;
				}
			}
			rtb.MouseUp += new MouseEventHandler(stv.Select);
			stv.ObjectChanged();
			return rtb;
		}

		public static Control NewBrowser(Model model) {
			TabControl tab = new TabControl();
			tab.Alignment = TabAlignment.Bottom;
			new SourceTabView(model, tab, new NewControl(ILTextView.NewControl));
			return tab;
		}


		public void Select(object o, MouseEventArgs args) {
			Select();
		}

		public void Select() {
			FindObject fo = new FindObject(tracking, rtb.SelectionStart, rtb.SelectionStart+rtb.SelectionLength);
			ASTVisitor visit = new ASTVisitor(fo.Visitor);
			this.ASTRoot.visit(visit);
			model.ChangeObject(fo.FoundObject);
		}

		public class FindObject {
			private Tracking tracking;
			private int lo;
			private int hi;
			public FindObject(Tracking tracking, int lo, int hi) {
				this.tracking = tracking;
				this.lo = lo;
				this.hi = hi;
			}
			public object FoundObject;
			public void Visitor(AST ast) {
				Tracking.Pair pair = tracking.Span(ast);
				if (pair != null && pair.begin <= lo && pair.end >= hi) {
					this.FoundObject = ast;
				}
			}
		}

		public class FindSpan {
			public Tracking.Pair pair;
			private Tracking tracking;
			public FindSpan(Tracking tracking) {
				this.tracking = tracking;
			}
			public void Visitor(AST ast) {
				Tracking.Pair span = tracking.Span(ast);
				if (span != null) {
					if (pair == null) {
						pair = span;
					} else {
						if (pair.begin > span.begin) pair.begin = span.begin;
						if (pair.end   < span.end)   pair.end   = span.end;
					}
				}
			}
		}

		public void ObjectChanged() {
			object o = model.CurrentObject;
			if (o != null && tracking != null) {
				Tracking.Pair span = null;
				if (o is AST) {
					AST ast = (AST) o;
					FindSpan fs = new FindSpan(tracking);
					ASTVisitor visit = new ASTVisitor(fs.Visitor);
					ast.visit(visit);
					span = fs.pair;
				}
				if (span != null) {
					rtb.SelectionLength = 0;
					rtb.SelectionStart = span.begin;
					rtb.SelectionLength = span.end - span.begin;
					rtb.HideSelection = false;
				} else {
					rtb.HideSelection = true;
				}
			} else {
				rtb.HideSelection = true;
			}
		}
	}
}

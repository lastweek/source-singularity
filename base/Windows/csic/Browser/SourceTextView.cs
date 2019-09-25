using System;
using System.IO;
using System.Windows.Forms;

namespace Browser
{
	/// <summary>
	/// Summary description for SourceTextView.
	/// </summary>
	public class SourceTextView {
		private AST ASTRoot;
		private string FName;

		private TextBox tb;
		private Model model;
		public SourceTextView(Model model, TextBox tb) {
			this.model = model;
			this.tb = tb;
			model.ObjectChangedHandler += new ObjectChangedEventHandler(this.ObjectChanged);
		}

		public static Control NewControl(Model model, object o) {
			IHasCoordinate ihc = (IHasCoordinate) o;
			TextBox tb = new TextBox();
			tb.WordWrap = false;
			tb.HideSelection = false;
			tb.Multiline = true;
			tb.ScrollBars = ScrollBars.Both;
			SourceTextView stv = new SourceTextView(model, tb);
			stv.FName = ihc.begin.file;
			if (ihc is AST) {
				AST p = (AST) ihc;
				while (p.parent != null && p.parent.begin.originalFile == ihc.begin.originalFile) {
					p = p.parent;
				}
				stv.ASTRoot = p;
			}
			StreamReader sr = new StreamReader(ihc.begin.originalFile);
			tb.Text = sr.ReadToEnd();
			tb.MouseUp += new MouseEventHandler(stv.Select);
			stv.ObjectChanged();
			return tb;
		}

		public void Select(object o, MouseEventArgs args) {
			Select();
		}

		public void Select() {
			Coordinate begin = new Coordinate(null, 0, 0, FName, tb.SelectionStart);
			Coordinate end   = new Coordinate(null, 0, 0, FName, tb.SelectionStart+tb.SelectionLength);
			if (ASTRoot != null) {
				AST node = ASTRoot.find(begin,end);
				if (node != null) {
					model.ChangeObject(node);
				}
			}
		}

		public void ObjectChanged() {
			object o = model.CurrentObject;
			tb.HideSelection = true;
			if (o is IHasCoordinate) {
				IHasCoordinate ihc = (IHasCoordinate) o;
				if (ihc.begin.originalFile == FName) {
					tb.SelectionStart = ihc.begin.fileOffset;
					tb.SelectionLength = ihc.end.fileOffset - ihc.begin.fileOffset;
					tb.HideSelection = false;
					tb.ScrollToCaret();
				}
			}
		}
	}
}

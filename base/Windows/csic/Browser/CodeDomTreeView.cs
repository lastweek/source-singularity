using System;
using System.CodeDom;
using System.Reflection;
using System.Collections;
using System.Windows.Forms;

namespace Browser {
	public class CodeDomTreeView {
		private TreeView tv;
		private Model model;
		private Hashtable o2n = new Hashtable();
		private CodeCompileUnit cu;

		public CodeDomTreeView(Model model, TreeView tv) {
			this.model = model;
			this.tv = tv;
			model.ObjectChangedHandler += new ObjectChangedEventHandler(this.ObjectChanged);
			tv.MouseUp += new MouseEventHandler(this.UserAfterSelect);
		}

		public static Control NewBrowser(Model model) {
			TabControl tab = new TabControl();
			tab.Alignment = TabAlignment.Bottom;
			new SourceTabView(model, tab, new NewControl(CodeDomTreeView.NewControl));
			return tab;
		}

		public static Control NewControl(Model model, object o) {
			IHasCoordinate ihc = (IHasCoordinate) o;
			TreeView tv = new TreeView();
			tv.HideSelection = false;
			CodeDomTreeView cdtv = new CodeDomTreeView(model, tv);
			if (ihc is AST) {
				cdtv.init((AST) ihc);
			}
			tv.MouseUp += new MouseEventHandler(cdtv.UserAfterSelect);
			cdtv.ObjectChanged();
			return tv;
		}

		public void UserAfterSelect(object o, MouseEventArgs argv) {
			UserAfterSelect();
		}

		public void UserAfterSelect() {
			object o = tv.SelectedNode.Tag;
			model.ChangeObject(o);
		}

		public void ObjectChanged() {
			object o = model.CurrentObject;
			if (o != null) {
				TreeNode tn = (TreeNode) o2n[o];
				if (tn != null) {
					tv.SelectedNode = tn;
				}
			} else {
			}
		}

		private void init(AST ast) {
			while (ast != null && !(ast is compilation_unit)) {
				ast = ast.parent;
			}
			if (ast != null) {
				cu = AST2CodeDom2.Compile((compilation_unit) ast);
				AddKid(cu, tv.Nodes, "", ast);
			}
		}

		private void AddKid(object o, TreeNodeCollection tnc, string name, AST key) {
			TreeNode n = new TreeNode();
			tnc.Add(n);
			if (o == null) {
				n.Text = name + ": null";
			} else {	// o != null
				System.Type t = o.GetType();
				if (o is CodeObject) {
					CodeObject co = (CodeObject) o;
					AST ast = (AST) co.UserData["AST"];
					int c = co.UserData.Count;
					if (ast != null && !o2n.Contains(ast)) {	// incredibly bogus because CodeDom synthesizes its own nodes!!  void type of property setter...
						o2n[ast] = n;
					}
					n.Tag = ast;
					foreach (PropertyInfo pi in t.GetProperties()) {
						if (pi.GetIndexParameters().Length == 0) {
							if (!(o is CodeObject) || pi.Name != "UserData") {
								object x = pi.GetValue(o, null);
								AddKid(x, n.Nodes, pi.Name, ast);
							}
						}
					}
					n.Text = name + ": " + t.ToString();
				} else if (o is IList) {
					IList a = (IList) o;
					if (a.Count > 0) {
						for (int i = 0; i < a.Count; i++) {
							object x = a[i];
							AddKid(x, n.Nodes, name + "["+i.ToString()+"]", key);
						}
						n.Tag = key;
						n.Text = name + ": " + t.ToString() + "{" + a.Count + "}";
					} else {
						tnc.Remove(n);
					}
				} else {
					n.Tag = key;
					n.Text = name + ": " + t.ToString() + " = " + o.ToString();
				}
			}
		}
	}
}

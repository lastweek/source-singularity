using System;
using System.Reflection;
using System.Collections;
using System.Windows.Forms;

namespace Browser {
	/// <summary>
	/// Summary description for ObjectTreeView.
	/// </summary>
	public class ObjectTreeView {
		private abstract class Thunk {
			public abstract string Text { get; }
			public abstract object Object { get; }
			public abstract TreeNode ThisNode { get; }
		}

		private class SimpleThunk : Thunk {
			private TreeNode thisNode;
			private object ovalue;
			private string text;
			public SimpleThunk(TreeNode thisNode, object ovalue, string text) {
				this.thisNode = thisNode;
				this.ovalue = ovalue;
				this.text = text;
			}
			public override TreeNode ThisNode {
				get { return thisNode; }
			}
			public override object Object {
				get { return ovalue; }
			}
			public override string Text {
				get { return text; }
			}
		}
		private class PropertyThunk : Thunk {
			private TreeNode thisNode;
			private object ovalue;
			private string text;
			private PropertyInfo property;
			private object self;
			private bool computed = false;
			public PropertyThunk(TreeNode thisNode, string text, PropertyInfo property, object self) {
				this.thisNode = thisNode;
				this.text = text;
				this.property = property;
				this.self = self;
			}
			public override TreeNode ThisNode {
				get {
					return thisNode;
				}
			}
			public override object Object {
				get { 
					if (!computed) {
						computed = true;
						try {
							ovalue = property.GetValue(self, null);
							thisNode.Text = property.Name + ": " + Identity(ovalue);
						} catch {
							ovalue = "<<exception thrown by property>>";
						}
					}
					return ovalue;
				}
			}
			public override string Text {
				get { return text; }
			}
		}

		private TreeNode previousNode;
		private TreeView tv;
		private Model model;
		private Hashtable o2thunk = new Hashtable();
		private Hashtable n2thunk = new Hashtable();

		public ObjectTreeView(Model model, TreeView tv) {
			this.model = model;
			this.tv = tv;
			tv.HideSelection = false;
			model.ObjectChangedHandler += new ObjectChangedEventHandler(this.ObjectChanged);
			tv.MouseUp += new MouseEventHandler(this.UserAfterSelect);
			this.ObjectChanged();
		}

		public static Control NewBrowser(Model model) {
			TreeView tv = new TreeView();
			new ObjectTreeView(model, tv);
			return tv;
		}

		public void UserAfterSelect(object o, MouseEventArgs argv) {
			UserAfterSelect();
		}

		public void UserAfterSelect() {
			if (tv.SelectedNode != previousNode && tv.SelectedNode != null) {
				Thunk thunk = (Thunk)n2thunk[tv.SelectedNode];
				model.ChangeObject(thunk.Object);
			}
		}

		public void ObjectChanged() {
			object o = model.CurrentObject;
			if (o != null && (tv.SelectedNode == null || !IsLeafType(o) || o != ((Thunk)n2thunk[tv.SelectedNode]).Object)) {
				Thunk thunk = AddRoot(o, tv);
				tv.SelectedNode = thunk.ThisNode;
			}
			previousNode = tv.SelectedNode;
		}

		private Thunk AddRoot(object o, TreeView tv) {
			if (o != null && o2thunk.Contains(o)) {
				return (Thunk)o2thunk[o];
			}
			TreeNode n = new TreeNode();
			if (o == null) {
				n.Text = "null";
				tv.Nodes.Add(n);
				Thunk t = new SimpleThunk(n, o, "null");
				n2thunk[n] = t;
				return t;
			}
			n.Text = "(" + o.GetType().Name + ") " + Identity(o);
			Thunk thunk = new SimpleThunk(n, o, n.Text);
			o2thunk[o] = thunk;
			n2thunk[n] = thunk;
			tv.Nodes.Add(n);
			AddMembers(o, n.Nodes);
			return thunk;
		}

		private Thunk AddKid(object o, TreeNodeCollection tnc, string name) {
			TreeNode n = new TreeNode();
			n.Text = name + ": " + Identity(o);
			tnc.Add(n);
			Thunk thunk = new SimpleThunk(n, o, n.Text);
			n2thunk[n] = thunk;
			if (o != null) {
				System.Type t = o.GetType();
				if (t.IsValueType && !IsLeafType(o)) {
					o2thunk[o] = thunk;
					AddMembers(o, n.Nodes);
				}
			}
			return thunk;
		}
		private Thunk AddPropertyKid(TreeNodeCollection tnc, PropertyInfo pi, object self) {
			TreeNode n = new TreeNode();
			n.Text = pi.Name + ": <property>";
			tnc.Add(n);
			Thunk thunk = new PropertyThunk(n, n.Text, pi, self);
			n2thunk[n] = thunk;
			return thunk;
		}


		private void AddMembers(object o, TreeNodeCollection tnc) {
			System.Type t = o.GetType();
			foreach (FieldInfo f in t.GetFields(bindingFlags)) {
				object i = f.GetValue(o);
				AddKid(i, tnc, f.Name);
			}
			foreach (PropertyInfo pi in t.GetProperties(bindingFlags)) {
				if (pi.GetIndexParameters().Length == 0) {
					AddPropertyKid(tnc, pi, o);
				}
			}
			if (o is IList) {
				IList a = (IList) o;
				for (int i = 0; i < a.Count; i++) {
					object x = a[i];
					AddKid(x, tnc, "["+i.ToString()+"]");
				}
			}
		}

		private static bool IsLeafType(object o) {
			if (o == null)
				return true;
			System.Type t = o.GetType();
			return o is string
				|| o is IImage
				//|| t.IsValueType 
				|| t.IsPrimitive
				// || o is ICollection && ((ICollection)o).Count == 0
				;
		}
		private static string Identity(object o) {
			if (o == null)
				return "null";
			if (o is IImage)
				return ((IImage)o).Image();
			else
				if (o is ICollection && ((ICollection)o).Count == 0)
				return String.Format("{0}#{1} (empty)", o.GetType().Name, o.GetHashCode());
			else if (IsLeafType(o))
				return o.ToString();
			else
				return String.Format("{0}#{1}", o.GetType().Name, o.GetHashCode());
		}
		private const BindingFlags bindingFlags = BindingFlags.Instance|BindingFlags.Public|BindingFlags.NonPublic;
	}
}

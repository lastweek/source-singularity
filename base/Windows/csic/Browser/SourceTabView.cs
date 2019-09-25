using System;
using System.Collections;
using System.Windows.Forms;

namespace Browser
{
	/// <summary>
	/// Summary description for SourceTabView.
	/// </summary>
	/// 
	public delegate Control NewControl(Model model, object o);

	public class SourceTabView
	{
		private Model model;
		private TabControl tab;
		private NewControl nc;
		private Hashtable files = new Hashtable();
		public SourceTabView(Model model, TabControl tab, NewControl nc) {
			this.model = model;
			this.tab = tab;
			this.nc = nc;
			model.ObjectChangedHandler += new ObjectChangedEventHandler(this.ObjectChanged);
			foreach (object o in model.Roots) {
				this.AddRoot(o);
			}
			this.ObjectChanged();
		}

		public void AddRoot(object root) {
			object o = root;
			if (o is IHasCoordinate) {
				IHasCoordinate ihc = (IHasCoordinate) o;
				string fname = ihc.begin.file;
				if (fname != null) {
					if (!files.Contains(fname)) {
						TabPage tp = new TabPage();
						tp.Text = fname;
						tab.Controls.Add(tp);
						Control ctl = nc(model, ihc);
						ctl.Dock = DockStyle.Fill;
						tp.Controls.Add(ctl);
						files[fname] = tp;
					}
				}
			}
		}

		public void ObjectChanged() {
			object o = model.CurrentObject;
			AddRoot(o);
			if (o is IHasCoordinate) {
				IHasCoordinate ihc = (IHasCoordinate) o;
				string fname = ihc.begin.file;
				if (fname != null) {
					if (!files.Contains(fname)) {
						tab.SelectedTab = (TabPage) files[fname];
					}
				}
			}
		}

	}
}

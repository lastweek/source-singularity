using System;
using System.IO;
using System.Text;
using System.Reflection;
using System.Collections;
using System.Windows.Forms;

namespace Browser {
	public delegate void ObjectChangedEventHandler();

	public class Model {
		private ArrayList roots = new ArrayList();
		public IEnumerable Roots {
			get { return roots; }
		}

		public Model(IEnumerable roots) {
			foreach (object o in roots) {
				this.roots.Add(o);
			}
		}

		private object _current = null;
		public object CurrentObject {
			get { return _current; }
		}

		public event ObjectChangedEventHandler ObjectChangedHandler;

		public void ChangeObject(object o) {
			if (o != null) {
				_current = o;
				ObjectChangedEventHandler oceh = ObjectChangedHandler;
				if (oceh != null) {
					oceh();
				}
			}
		}
	}
}
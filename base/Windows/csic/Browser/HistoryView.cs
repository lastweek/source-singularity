using System;
using System.Collections;

namespace Browser
{
	/// <summary>
	/// Summary description for History.
	/// </summary>
	public class HistoryView
	{
		private Stack backHistory = new Stack();
		private Stack forwardHistory = new Stack();
		private Model model;
		public HistoryView(Model model) {
			this.model = model;
			model.ObjectChangedHandler += new ObjectChangedEventHandler(this.ObjectChanged);
		}

		public void Back() {
			if (backHistory.Count > 1) {
				forwardHistory.Push(backHistory.Pop());
				object o = backHistory.Peek();
				model.ChangeObject(o);
			}
		}
		public void Forward() {
			if (forwardHistory.Count > 0) {
				backHistory.Push(forwardHistory.Pop());
				object o = backHistory.Peek();
				model.ChangeObject(o);
			}
		}

		public void ObjectChanged() {
			object o = model.CurrentObject;
			if (backHistory.Count == 0 || backHistory.Peek() != o) {
				backHistory.Push(o);
				forwardHistory.Clear();
			}
		}
	}
}

using System;

namespace Browser {
	public class ParentView {
		private Model model;
		public ParentView(Model model) {
			this.model = model;
		}

		public void Parent() {
			object current = model.CurrentObject;
			if (current != null && current is AST) {
				AST ast = (AST) current;
				if (ast.parent != null) {
					model.ChangeObject(ast.parent);
				}
			}
		}
	}
}

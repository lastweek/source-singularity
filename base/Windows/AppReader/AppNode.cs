// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace AppReader
{
    using System;
    using System.Collections;
    using System.Diagnostics;
    using System.IO;

	public class AppNode
	{
		ArrayList children;
		string nodeName;
		AppNode parent;
		int count;
		// whether or not we've already added our childrens' weights to ours
		bool normalized;

		public AppNode(string nodeName, AppNode parent)
		{
			this.nodeName = nodeName;
			this.parent = parent;
			if (parent != null)
				parent.AddChild(this);
			count = 0;
			this.children = new ArrayList();
			normalized = false;
		}

		public string Name
		{
			get { return nodeName; }
		}

		public int NumChildren
		{
			get { return children.Count; }
		}

		public AppNode Parent
		{
			get { return parent; }
		}
	
		public void Dump(string indent)
		{
			Console.WriteLine(indent + nodeName + ": " + count);
			for (int i = 0; i < children.Count; i++)
			{
				((AppNode)children[i]).Dump(indent + "\t");
			}
		}
	
		public AppNode Copy(AppNode inParent)
		{
			AppNode outnode = new AppNode(this.nodeName, inParent);
			outnode.count = this.count;
			outnode.normalized = this.normalized;
			for (int i = 0; i < this.children.Count; i++)
			{
				// this looks like a throwaway, but in the constructor it will attach to us
				((AppNode)this.children[i]).Copy(outnode);
			}
			return outnode;
		}

		public void AddChild(AppNode child)
		{
			children.Add(child);
			return;
		}

		public void Increment(int amount)
		{
			this.count += amount;
			return;
		}

		public AppNode this[int index]
		{
			get
			{
				return (AppNode)children[index];
			}
			set
			{
				children[index] = value;
				return;
			}
		}

		public int Weight()
		{
			if (normalized) return this.count;
			normalized = true;
			for (int i = 0; i < this.children.Count; i++)
			{
				this.count += ((AppNode)this.children[i]).Weight();
			}
			return this.count;
		}
	
		public void Flatten(ArrayList ar)
		{
			// put all our children in it before we go in (post-order)
			for (int i = 0; i < this.children.Count; i++)
			{
				((AppNode)this.children[i]).Flatten(ar);
			}
			ar.Add(this);
			return;
		}

	}
}

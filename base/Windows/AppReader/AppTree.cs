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

	public class AppTree
	{
		AppNode top;
		public AppTree(AppNode top)
		{
			this.top = top;
		}

		public AppTree(AppTree other)
		{
			// we just walk the other tree and get a new copy
			this.top = other.top.Copy(null);
		}

		public void IncrementNode(string treePath)
		{
			IncrementNode(treePath, 1);
			return;
		}

		public void IncrementWithHashtable(Hashtable whash)
		{
			// a hashtable of paths in the tree and the weights of their endpoints
			// we just walk through the things we found and increment them in the tree
			// if they exist in the wxvals hashtable
			IEnumerator ienum = whash.GetEnumerator();
			while (ienum.MoveNext())
			{
				string key = (string)((DictionaryEntry)ienum.Current).Key;
				int val = (int)((DictionaryEntry)ienum.Current).Value;
				this.IncrementNode(key, val);
			}
			return;
		}

		public void Dump()
		{
			if (top != null)
			{
				Console.WriteLine("\nAppTree");
				top.Dump("");
			}
			return;
		}

		// this method converts a tree to a representation over which we can do clustering.
		// We add the sum of the weights of the children to the weight of their parent
		// so that we preserve the tree structure in the data, and then we do a post-order
		// traversal of the tree to get our ArrayList of weights.  It is thus critical that
		// all trees have the same structure and order, but our code guarantees this property.
		public ArrayList Flatten()
		{
			ArrayList ar = new ArrayList();
			AppTree treeToFlatten = new AppTree(this);
			treeToFlatten.top.Weight();
			treeToFlatten.top.Flatten(ar);
			return ar;
		}

		public void IncrementNode(string treePath, int count)
		{
			// HACK: 10 is a magic number.  I just don't think 
			// my resource trees will ever be 10 deep
			string[] pathstr = treePath.Split(new char[] {' '}, 10);
			AppNode curNode = top;
			for (int i = 0; i < pathstr.Length; i++)
			{
				if (pathstr[i].Equals("")) continue;
				// find the child that has the right name
				bool found = false;
				for (int j = 0; j < curNode.NumChildren; j++)
				{
					if (curNode[j].Name == pathstr[i])
					{
						curNode = curNode[j];
						found = true;
						break;
					}
				}
				Debug.Assert(found);
			}
			curNode.Increment(count);
			return;
		}

		public static AppTree CreateAppTree(string filename)
		{
			// parse the app tree structure here
			StreamReader ios = new StreamReader(filename);
			string curLine;
			// this is the first node we create
			AppNode top = null;
			AppNode lastNode = null;
			int lastTabCount = 0;
			while ((curLine = ios.ReadLine()) != null)
			{
				int tabcount = curLine.LastIndexOf("\t");
				tabcount++;
				//Console.WriteLine("Got tabcount {0}", tabcount);
				Debug.Assert(tabcount >= 0);

				string name = curLine.Substring(tabcount);
				AppNode parent = lastNode == null ? null : lastNode.Parent;
				if (tabcount < lastTabCount)
				{
					// then walk up the tree to the new parent
					int diff = lastTabCount - tabcount;
					while (diff-- > 0)
					{
						parent = parent.Parent;
						Debug.Assert(parent != null);
					}
				}
				else if (tabcount > lastTabCount) {
					parent = lastNode;
					Debug.Assert(tabcount == lastTabCount + 1);
				}
				// this automatically joins this node to its parent in the tree
				AppNode tempNode = new AppNode(name, parent);
				if (top == null)
				{
					Debug.Assert(tabcount == 0);
					top = tempNode;
				}
				lastNode = tempNode;
				lastTabCount = tabcount;
			}	
			AppTree outtree = new AppTree(top);
			return outtree;
		}
	}

}

////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

using System;
using System.Diagnostics;
using System.IO;

namespace Microsoft.Singularity.Applications
{
    public class TreeTestBase { }

    public class MkUnionTest
    {
        public static int SumTree(Tree tree) {
            switch (tree.Tag) {
                case Tree.TagValue.Leaf:
                    return 0;
                case Tree.TagValue.Node:
                    Tree.Node node = tree.GetAsNode();
                    return node.Value + SumTree(node.Left) + SumTree(node.Right);
                default:
                    Debug.Assert(false, "Unhandled alternative in switch over 'Tree'");
                    return 0;
            }
        }

        public static void Main() {
            Tree tree = Tree.CreateNode(5, Tree.CreateNode(3, Tree.CreateLeaf(), Tree.CreateLeaf()),
                                           Tree.CreateNode(8, Tree.CreateLeaf(), Tree.CreateLeaf()));
            Console.WriteLine("Sum of tree nodes is " + SumTree(tree));
            TreeTestBase testBase = (TreeTestBase)tree; // Should compile
            Tree.Bar(); // Prints "Bar"
        }
    }
}

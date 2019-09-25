///////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

using System;
using System.Collections;
using System.Diagnostics;
using System.Text;

namespace Microsoft.Singularity.Hal.Acpi
{
    public class AcpiNamespace
    {
        /// <summary>
        /// The absolute or relative location of a node in the ACPI namespace.
        /// </summary>
        public class NodePath
        {
            bool isAbsolute;
            int numParentPrefixes;
            string[] nameSegments;

            public NodePath(bool isAbsolute, int numParentPrefixes, string[] nameSegments)
            {
                Debug.Assert(numParentPrefixes >= 0, "numParentPrefixes >= 0");
                Debug.Assert(!isAbsolute || numParentPrefixes == 0,
                             "Absolute path cannot have parent prefixes");
                Debug.Assert(nameSegments.Length >= 0);

                foreach (string name in nameSegments) {
                    AssertIsValidName(name);
                }

                this.isAbsolute = isAbsolute;
                this.numParentPrefixes = numParentPrefixes;
                this.nameSegments = nameSegments;
            }

            public bool IsAbsolute
            {
                get
                {
                    return isAbsolute;
                }
            }

            public int NumParentPrefixes
            {
                get
                {
                    return numParentPrefixes;
                }
            }

            public string[] NameSegments
            {
                get
                {
                    return nameSegments;
                }
            }

            public NodePath AddSegment(string segment)
            {
                string[] resultNameSegments = new string[this.nameSegments.Length + 1];
                for (int i = 0; i < this.nameSegments.Length; i++) {
                    resultNameSegments[i] = (string)this.nameSegments[i];
                }
                resultNameSegments[resultNameSegments.Length - 1] = segment;
                return new NodePath(IsAbsolute, NumParentPrefixes, resultNameSegments);
            }

            public NodePath RemoveSegment()
            {
                string[] resultNameSegments = new string[this.nameSegments.Length - 1];
                for (int i = 0; i < this.nameSegments.Length - 1; i++) {
                    resultNameSegments[i] = (string)this.nameSegments[i];
                }
                return new NodePath(IsAbsolute, NumParentPrefixes, resultNameSegments);
            }

            public override string ToString()
            {
                StringBuilder builder = new StringBuilder();
                for (int i = 0; i < nameSegments.Length - 1; i++) {
                    builder.Append(nameSegments[i]);
                    builder.Append("\\");
                }
                if (nameSegments.Length > 0) {
                    builder.Append(nameSegments[nameSegments.Length - 1]);
                }
                return builder.ToString();
            }
        }

        /// <summary>
        /// A restricted type of NodePath that must be statically absolute.
        /// </summary>
        /// <remarks>Not every absolute path has this type - some are AbsoluteNodePaths
        /// and some are NodePaths. The purpose of this subclass is to statically enforce
        /// that absolute paths are always used in certain limited contexts.</remarks>
        public class AbsoluteNodePath : NodePath
        {
            public AbsoluteNodePath(string[] nameSegments)
                : base(false, 0, nameSegments) { }

            public static AbsoluteNodePath CreateRoot()
            {
                return new AbsoluteNodePath(new string[] { });
            }

            public AbsoluteNodePath AddSegmentAbsolute(string segment)
            {
                return new AbsoluteNodePath(AddSegment(segment).NameSegments);
            }

            public AbsoluteNodePath RemoveSegmentAbsolute()
            {
                return new AbsoluteNodePath(RemoveSegment().NameSegments);
            }
        }

        /// <summary>
        /// A node in the ACPI namespace tree.
        /// </summary>
        public class Node
        {
            private string name;
            private Node parentNode;
            private IDictionary childByNameMap = null;
            private AcpiObject.AcpiObjectCell value;

            /// <summary>
            /// Create a root node.
            /// </summary>
            public Node()
            {
                this.name = "";
                this.parentNode = null;
                this.value = new AcpiObject.AcpiObjectCell(new AcpiObject.UninitializedObject());
            }

            /// <summary>
            /// Create a child node with a given name and parent node.
            /// </summary>
            public Node(string name, Node parentNode)
            {
                AssertIsValidName(name);
                Debug.Assert(parentNode != null);
                this.name = name;
                this.parentNode = parentNode;
                this.value = new AcpiObject.AcpiObjectCell(new AcpiObject.UninitializedObject());
                parentNode.AddChild(this);
            }

            /// <summary>
            /// Makes this node refer to the same value as the given node.
            /// </summary>
            /// <remarks>Aliased names refer to not only the same object but
            /// the same object location (cell). Any updates to either node
            /// immediately appear in the other.</remarks>
            public void AliasTo(Node n)
            {
                this.value = n.value;
            }

            private void AddChild(Node child)
            {
                Debug.Assert(child.parentNode == this);
                if (childByNameMap == null) {
                    childByNameMap = new SortedList();
                }
                Debug.Assert(!childByNameMap.Contains(child.name));
                childByNameMap.Add(child.name, child);
            }

            public Node ParentNode
            {
                get
                {
                    return parentNode;
                }
            }

            public string Name
            {
                get
                {
                    return name;
                }
            }

            public Node GetChildByName(string name)
            {
                if (childByNameMap != null && childByNameMap.Contains(name)) {
                    return (Node)childByNameMap[name];
                }
                else {
                    return null;
                }
            }

            public AcpiObject.AcpiObject Value
            {
                get
                {
                    return value.Value;
                }
                set
                {
                    this.value.Value = value;
                }
            }

            public void Remove()
            {
                if (childByNameMap != null) {
                    foreach (Node child in childByNameMap.Values) {
                        child.Remove();
                    }
                }
                if (this.parentNode != null) {
                    this.parentNode.childByNameMap.Remove(name);
                }
            }

            public AbsoluteNodePath Path
            {
                get
                {
                    // Measure how deep this node's path is
                    int level = 0;
                    Node n = parentNode;
                    while (n != null) {
                        level++;
                        n = n.parentNode;
                    }

                    // Build the path
                    string[] nameSegments = new string[level];
                    n = this;
                    for(int i = nameSegments.Length - 1; i >= 0; i--) {
                        nameSegments[i] = n.name;
                        n = n.parentNode;
                    }

                    return new AbsoluteNodePath(nameSegments);
                }
            }

            public int CountSubtreeNodes()
            {
                int count = 1;
                if (childByNameMap != null) {
                    foreach (Node child in childByNameMap.Values) {
                        count += child.CountSubtreeNodes();
                    }
                }
                return count;
            }

            public void GetSubtreeNodes(Node[] result, ref int startIndex)
            {
                result[startIndex] = this;
                startIndex++;

                if (childByNameMap != null) {
                    foreach (Node child in childByNameMap.Values) {
                        child.GetSubtreeNodes(result, ref startIndex);
                    }
                }
            }

            public Node FindValue(AcpiObject.AcpiObject value)
            {
                if (this.Value == value) {
                    return this;
                }
                else if (childByNameMap != null) {
                    foreach (Node child in childByNameMap.Values) {
                        Node result = child.FindValue(value);
                        if (result != null) {
                            return result;
                        }
                    }
                }
                return null;
            }

            public override string ToString()
            {
                return Path.ToString();
            }

            public void DumpSubtree()
            {
#if SINGULARITY_KERNEL
                DebugStub.WriteLine(this.ToString());
#else
                Console.WriteLine(this.ToString());
#endif
                if (childByNameMap != null) {
                    foreach (Node child in childByNameMap.Values) {
                        child.DumpSubtree();
                    }
                }
            }
        }

        public class NodeAlreadyExistsException : Exception
        {
            public NodeAlreadyExistsException()
                : base("Node already exists")
            {
            }

            public NodeAlreadyExistsException(string message)
                : base("Node already exists: " + message)
            {
            }
        }

        private Node rootNode = new Node();

        public AcpiNamespace()
        {
        }

        /// <summary>
        /// Look up the node at a given absolute node path.
        /// </summary>
        /// <returns>The requested node, or null if the node is not found.</returns>
        public Node LookupNode(AbsoluteNodePath nodePath)
        {
            return LookupDescendantNode(rootNode, nodePath.NameSegments);
        }

        /// <summary>
        /// Look up the node at a given absolute or relative node path.
        /// This may include "single segment name" paths which invoke the
        /// search strategy described in section 5.3 of the ACPI spec 3.0b.
        /// </summary>
        /// <param name="currentPath">Absolute path of the current path
        /// relative to which any relative node path will be determined.</param>
        /// <returns>The requested node, or null if the node is not found.</returns>
        public Node LookupNode(NodePath nodePath, AbsoluteNodePath currentPath)
        {
            if (nodePath.IsAbsolute) {
                return LookupDescendantNode(rootNode, nodePath.NameSegments);
            }
            else {
                Node startNode = LookupNode(currentPath);
                Debug.Assert(startNode != null, "LookupNode: Current path did not resolve");

                if (nodePath.NumParentPrefixes > 0) {
                    for (int i = 0; i < nodePath.NumParentPrefixes; i++) {
                        startNode = startNode.ParentNode;
                        if (startNode == null) {
                            throw new ArgumentException("Relative path attempts to move above root");
                        }
                    }
                    return LookupDescendantNode(startNode, nodePath.NameSegments);
                }
                else {
                    // The search rules apply - try successively larger scopes
                    while (startNode != null) {
                        Node result = LookupDescendantNode(startNode, nodePath.NameSegments);
                        if (result != null) {
                            return result;
                        }
                        startNode = startNode.ParentNode;
                    }
                    return null;
                }
            }
        }

        /// <summary>
        /// A version of LookupNode that does not ever apply the search rules.
        /// </summary>
        private Node LookupNodeNoSearch(NodePath nodePath, AbsoluteNodePath currentPath)
        {
            if (nodePath.IsAbsolute) {
                return LookupDescendantNode(rootNode, nodePath.NameSegments);
            }
            else {
                Node startNode = LookupNode(currentPath);
                Debug.Assert(startNode != null, "LookupNode: Current path did not resolve");

                for (int i = 0; i < nodePath.NumParentPrefixes; i++) {
                    startNode = startNode.ParentNode;
                    if (startNode == null) {
                        throw new ArgumentException("Relative path attempts to move above root");
                    }
                }
                return LookupDescendantNode(startNode, nodePath.NameSegments);
            }
        }

        private Node LookupDescendantNode(Node node, string[] nameSegments)
        {
            Node n = node;
            foreach (string name in nameSegments) {
                n = n.GetChildByName(name);
                if (n == null) {
                    break;
                }
            }
            return n;
        }

        public Node CreateNodeAt(NodePath nodePath, AbsoluteNodePath currentPath)
        {
            if (LookupNodeNoSearch(nodePath, currentPath) != null) {
                throw new NodeAlreadyExistsException();
            }

            // Find deepest existing node on the path
            NodePath ancestorNodePath = nodePath;
            Node ancestorNode;
            int stepsUp = 0;
            do {
                ancestorNodePath = ancestorNodePath.RemoveSegment();
                stepsUp++;
                ancestorNode = LookupNodeNoSearch(ancestorNodePath, currentPath);
            } while (ancestorNode == null);

            // Create remaining names to get a node with the desired path
            Node newNode = null;
            string[] nameSegments = nodePath.NameSegments;
            for (int i = nameSegments.Length - stepsUp; i < nameSegments.Length; i++) {
                newNode = new Node((string)nameSegments[i], ancestorNode);
                ancestorNode = newNode;
            }

            return newNode;
        }

        public Node FindValue(AcpiObject.AcpiObject value)
        {
            return rootNode.FindValue(value);
        }

        public Node[] GetAllNodes()
        {
            Node[] result = new Node[rootNode.CountSubtreeNodes()];
            int startIndex = 0;
            rootNode.GetSubtreeNodes(result, ref startIndex);
            return result;
        }

        private static void AssertIsValidName(string name)
        {
            Debug.Assert(IsValidName(name), "Invalid name for ACPI namespace node");
        }

        public void DumpTree()
        {
            rootNode.DumpSubtree();
        }
            
        internal static bool IsValidName(byte[] name)
        {
            return name.Length == 4 &&
                   (Char.IsUpper((char)name[0]) || (char)name[0] == '_') &&
                   (Char.IsUpper((char)name[1]) || (char)name[1] == '_' || Char.IsDigit((char)name[1])) &&
                   (Char.IsUpper((char)name[2]) || (char)name[2] == '_' || Char.IsDigit((char)name[2])) &&
                   (Char.IsUpper((char)name[3]) || (char)name[3] == '_' || Char.IsDigit((char)name[3]));
        }

        internal static bool IsValidName(string name)
        {
            return name.Length == 4 &&
                   (Char.IsUpper(name[0]) || name[0] == '_') &&
                   (Char.IsUpper(name[1]) || name[1] == '_' || Char.IsDigit(name[1])) &&
                   (Char.IsUpper(name[2]) || name[2] == '_' || Char.IsDigit(name[2])) &&
                   (Char.IsUpper(name[3]) || name[3] == '_' || Char.IsDigit(name[3]));
        }
    }
}

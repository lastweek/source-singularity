// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace Microsoft.Singularity.Xml
{
    using System;
    using System.Collections;
    using System.Globalization;

    /// <summary>
    /// Summary description for XmlNode.
    /// </summary>
    public class XmlNode
    {
        private string name;
        private int depth;
        private string text;
        private ArrayList attributes;
        private ArrayList children;
        private XmlNode parentNode;

       internal class XmlAttr
        {
           public readonly string name;
            public  string value;

            internal XmlAttr(string name, string value)
            {
                this.name = name != null ? name : "";
                this.value = value;
            }
            internal void WriteContentTo(XmlWriter w)
            {
                w.WriteString(this.value);
            }

            internal void WriteTo(XmlWriter w)
            {
                //w.WriteAttributeString(this.name, this.value);
                w.WriteStartAttribute(null, this.name, null);
                WriteContentTo(w);
                w.WriteEndAttribute();
            }
        }

        public XmlNode()
        {
            attributes = new ArrayList();
            children = new ArrayList();
            this.text = "";
        }

        public XmlNode(string name)
        {
            this.name = name != null ? name : "";
            attributes = new ArrayList();
            children = new ArrayList();
            this.text = "";
        }

       internal virtual XmlNode NullNode {
            get {
                return null;
            }
        }
        public void SetParent(XmlNode p)
        {
            this.parentNode = p;
        }

        public virtual XmlNode ParentNode
        {
            get
            {
                if (parentNode == NullNode)
                    return null;
                return parentNode;
            }
        }

        public XmlNode(string name, int depth)
        {
            this.name = name;
            this.depth = depth;
            attributes = new ArrayList();
            children = new ArrayList();
            this.text = "";
        }

        public XmlNode[] Children
        {
            get
            {
                XmlNode[] result;
                if (children == null) {
                    result = new XmlNode[0];
                }
                else {
                    if (children.Count == 0) {
                        result = new XmlNode[0];
                    }
                    else {
                        result = new XmlNode[children.Count];
                        int i = 0;
                        foreach (XmlNode childNode in children) {
                            result[i++] = childNode;
                        }
                    }
                }

                return result;
            }
        }

        public XmlNode CreateNode (string name)
        {
            XmlNode n = new XmlNode();
            n.name = name;
            return n;
        }

        public XmlNode[] ChildNodes
        {
            get { return this.Children ;}

        }
        public ArrayList GetNamedChildren(string name)
        {
            ArrayList result = new ArrayList();
            foreach (XmlNode childNode in children) {
                if (childNode.Name == name) {
                    result.Add(childNode);
                }
            }
            return result;
        }

        public XmlNode GetChild(string name)
        {
            foreach (XmlNode childNode in children) {
                if (childNode.Name == name) {
                    return childNode;
                }
            }
            return null;
        }

        public XmlNode GetNestedChild(String[] childNames)
        {
            XmlNode node = this;

            for (int i = 0; node != null && i < childNames.Length; i++) {
                node = node.GetNestedChild(childNames[i]);
            }
            return node;
        }

        public XmlNode GetNestedChild(String childName)
        {
            foreach (XmlNode childNode in children) {
                if (childNode.Name == childName) {
                    return childNode;
                }
            }
            return null;
        }

        // override this
        /// <devdoc>
        ///    <para>Saves the current node to the specified XmlWriter.</para>
        /// </devdoc>
        public virtual void WriteTo(XmlWriter w)
        {
            if (this.name == "::xml") {
                WriteContentTo(w);
                return;
            }

            w.WriteStartElement("", this.name, "");

            if (attributes.Count > 0) {
                foreach (XmlAttr attr in attributes) {
                    attr.WriteTo(w);
                }
            }

            if (children.Count > 0) {
                WriteContentTo(w);
            }
            if (children.Count == 0)
                w.WriteEndElement();
            else
                w.WriteFullEndElement();
        }

        // override this
        /// <devdoc>
        ///    <para>Saves all the children of the node to the specified XmlWriter.</para>
        /// </devdoc>
        public virtual void WriteContentTo(XmlWriter w)
        {
            foreach (XmlNode n in children) {
                n.WriteTo(w);
            }
        }

        public int Depth
        {
            get { return depth; }
        }

        public string Name
        {
            get { return name; }
        }

        public void AddChild(XmlNode node)
        {
            children.Add(node);
            return;
        }

        public ArrayList ChildrenList
        {
            get { return new ArrayList(children); }
        }

        public void AddText(string text)
        {
            this.text += text;
            return;
        }

        public string Text
        {
            get { return text; }
        }

        public string this[string attributeName]
        {
            get
            {
                XmlAttr a = FindAttr(attributeName);
                if (a == null) return null;
                return a.value;
            }
            set
            {
                XmlAttr a = FindAttr(attributeName);
                if (a == null) {
                    a = new XmlAttr(attributeName, value);
                    attributes.Add(a);
                }
                else a.value = value;
            }
        }

        //
        // Safe access to attributes:
        //      since the kernel is going to use this object, we should
        //      push the error-checking into the object instead of risking
        //      the kernel forgetting to error check in some obscure method
        //

        public string GetAttribute(string attributeName, string defaultValue)
        {
            XmlAttr a = FindAttr(attributeName);
            if (a == null) {
                return defaultValue;
            }
            else {
                return a.value;
            }
        }

        public bool GetAttribute(string attributeName, bool defaultValue)
        {
            XmlAttr a = FindAttr(attributeName);
            if (a == null) {
                return defaultValue;
            }
            else {
                return a.value ==
                    System.Boolean.TrueString;
            }
        }

        public int GetAttribute(string attributeName, int defaultValue)
        {
            XmlAttr a = FindAttr(attributeName);
            if (a == null) {
                return defaultValue;
            }
            else {
                string num = a.value;
                if (num.StartsWith("0x") || num.StartsWith("0X")) {
                    return System.Int32.Parse(num, NumberStyles.AllowHexSpecifier);
                }
                else {
                    return System.Int32.Parse(num);
                }
            }
        }

        public long GetAttribute(string attributeName, long defaultValue)
        {
            XmlAttr a = FindAttr(attributeName);
            if (a == null) {
                return defaultValue;
            }
            else {
                string num = a.value;
                if (num.StartsWith("0x") || num.StartsWith("0X")) {
                    return System.Int64.Parse(num, NumberStyles.AllowHexSpecifier);
                }
                else {
                    return System.Int64.Parse(num);
                }
            }
        }

        [CLSCompliant(false)]
        public UIntPtr GetAttributeAsUIntPtr(string attributeName, UIntPtr defaultValue)
        {
            XmlAttr a = FindAttr(attributeName);
            if (a == null) {
                return defaultValue;
            }
            else {
                string num = a.value;
                if (num.StartsWith("0x") || num.StartsWith("0X")) {
                    return System.UIntPtr.Parse(num, NumberStyles.AllowHexSpecifier);
                }
                else {
                    return System.UIntPtr.Parse(num);
                }
            }
        }

        public void PrependAttribute(string name, string value)
        {
            if (attributes == null) return;
            XmlAttr a = new XmlAttr(name,value);
            attributes.Insert(0,a);
        }

        public void AddAttribute(string name, string value)
        {
            if (attributes == null) return;
            XmlAttr a = new XmlAttr(name, value);
            attributes.Add(a);
        }

        public bool HasAttribute(string attributeName)
        {
            return (FindAttr(attributeName) != null) ;
        }

        private XmlAttr FindAttr(string name)
        {
            if (attributes == null) return null;
            foreach (XmlAttr attr in attributes) {
                if (attr.name == name) return attr;
            }
            return null;
        }

        public string GetAttributes()
        {
            string list = "";

            foreach (DictionaryEntry entry in attributes) {
                list = list + " " + entry.Key.ToString() + "=\"" + entry.Value.ToString() + "\"";
            }
            return list;
        }
    }
}

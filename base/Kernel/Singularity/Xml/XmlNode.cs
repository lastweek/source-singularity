//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Libraries\Xml\XmlNode.cs
//
//////////////////////////////////////////////////////////////////////////////

using System;
using System.Globalization;
using System.Text;

namespace Microsoft.Singularity.Xml
{
    /// <summary>
    /// Summary description for XmlNode.
    /// </summary>
    public class XmlNode
    {
        internal struct XmlAttr
        {
            internal readonly string name;
            internal readonly string value;

            internal XmlAttr(string name, string value)
            {
                this.name = name != null ? name : "";
                this.value = value;
            }
        }

        private const int   defaultAttributesCapacity = 8;
        private const int   defaultChildrenCapacity = 8;

        private readonly string name;
        private string          text;
        private XmlAttr[]       attributes;
        private int             attributesUsed;
        private XmlNode[]       children;
        private int             childrenUsed;

        public XmlNode(string name)
        {
            this.name = name != null ? name : "";
            this.text = "";
        }

        public int CountNamedChildren(string name)
        {
            int result = 0;
            XmlNode[] childs = Children;
            foreach (XmlNode child in childs) {
                if (child.Name == name) {
                    result++;
                }
            }
            return result;
        }

        public XmlNode GetChild(String[] childNames)
        {
            XmlNode node = this;

            for (int i = 0; node != null && i < childNames.Length; i++) {
                node = node.GetChild(childNames[i]);
            }
            return node;
        }

        public XmlNode GetChild(String childName)
        {
            XmlNode[] childs = Children;
            foreach (XmlNode child in childs) {
                if (child.Name == childName) {
                    return child;
                }
            }
            return null;
        }

        public string Name
        {
            get { return name; }
        }

        public void AddChild(XmlNode node)
        {
            if (children == null) {
                children = new XmlNode[defaultChildrenCapacity];
            }
            else if (childrenUsed == children.Length) {
                XmlNode[] dest = new XmlNode[childrenUsed * 2];
                for (int i = 0; i < childrenUsed; i++) {
                    dest[i] = children[i];
                }
                children = dest;
            }
            children[childrenUsed++] = node;
        }

        public string  GetAttribute(string name)
        {
            return this[name];
        }
        
        public XmlNode CreateNode (string name)
        {
            return new XmlNode(name);
        }
        
        public XmlNode[] ChildNodes
        {
            get { return this.Children ;}
        }
        public XmlNode[] Children
        {
            get {
                if (children == null) {
                    children = new XmlNode[0];
                }
                else if (childrenUsed != children.Length) {
                    // optimize for the case that the XML tree is read once
                    // and then remains static.
                    XmlNode[] dest = new XmlNode[childrenUsed];
                    for (int i = 0; i < childrenUsed; i++) {
                        dest[i] = children[i];
                    }
                    children = dest;
                }
                return children;
            }
        }

        public void AddText(string text)
        {
            this.text += text;
        }

        public string Text
        {
            get { return text; }
        }

        public string this[string attributeName]
        {
            get
            {
                for (int i = 0; i < attributesUsed; i++) {
                    if (attributes[i].name == attributeName) {
                        return attributes[i].value;
                    }
                }
                return null;
            }
        }

        public void AddAttribute(string name, string value)
        {
            if (attributes == null) {
                attributes = new XmlAttr[defaultAttributesCapacity];
            }
            else if (attributesUsed == attributes.Length) {
                XmlAttr[] dest = new XmlAttr[attributesUsed * 2];
                for (int i = 0; i < attributesUsed; i++) {
                    dest[i] = attributes[i];
                }
                attributes = dest;
            }
            attributes[attributesUsed++] = new XmlAttr(name, value);
        }

        public void PrependAttribute(string name, string value)
        {
            if (attributes == null) {
                attributes = new XmlAttr[defaultAttributesCapacity];
            }
            else if (attributesUsed == attributes.Length) {
                XmlAttr[] dest = new XmlAttr[attributesUsed * 2];
                for (int i = 0; i < attributesUsed; i++) {
                    dest[i+1] = attributes[i];
                }
                attributes = dest;
            }
            else {
                //shift everything up one
                for (int i = attributesUsed; i > 0; i--) {
                    attributes[i] = attributes[i-1];
                }
            }
            attributes[0] = new XmlAttr(name, value);
            attributesUsed++;
        }

        //
        // Safe access to attributes:
        //      since the kernel is going to use this object, we should
        //      push the error-checking into the object instead of risking
        //      the kernel forgetting to error check in some obscure method
        //

        public string GetAttribute(string attributeName, string defaultValue)
        {
            string value = this[attributeName];
            if (value == null) {
                return defaultValue;
            }
            return value;
        }

        public bool GetAttribute(string attributeName, bool defaultValue)
        {
            string value = this[attributeName];
            if (value == null) {
                return defaultValue;
            }
            return (value == "true" || value == "True");
        }

        public int GetAttribute(string attributeName, int defaultValue)
        {
            string value = this[attributeName];
            if (value == null) {
                return defaultValue;
            }
            if (value.StartsWith("0x") || value.StartsWith("0X")) {
                return System.Int32.Parse(value, NumberStyles.AllowHexSpecifier);
            }
            else {
                return System.Int32.Parse(value);
            }
        }

        [CLSCompliant(false)]
        public UIntPtr GetAttributeAsUIntPtr(string attributeName, UIntPtr defaultValue)
        {
            string value = this[attributeName];
            if (value == null) {
                return defaultValue;
            }
            if (value.StartsWith("0x") || value.StartsWith("0X")) {
                return System.UIntPtr.Parse(value, NumberStyles.AllowHexSpecifier);
            }
            else {
                return System.UIntPtr.Parse(value);
            }
        }

        public bool HasAttribute(string attributeName)
        {
            return this[attributeName] != null;
        }

        public string GetAttributes()
        {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < attributesUsed; i++) {
                sb.Append(" ");
                sb.Append(attributes[i].name);
                sb.Append("=\"");
                sb.Append(attributes[i].value);
                sb.Append("\"");
            }
            return sb.ToString();
        }
    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml;
using System.Diagnostics;

namespace NuBuild
{
    class Disposition
    {
        public virtual IEnumerable<string> getMessages() { return new string[0]; }

        protected virtual void writeXmlExtend(XmlWriter xw)
        {
        }

        public virtual void writeXml(XmlWriter xw)
        {
            xw.WriteStartElement(_xml_tag);
            xw.WriteAttributeString(_xml_value_attr, ToString());
            writeXmlExtend(xw);
            xw.WriteEndElement();
        }


        public const string _xml_tag = "Disposition";
        const string _xml_value_attr = "Value";

        public static Disposition readXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(_xml_tag));
            string value = xr.GetAttribute(_xml_value_attr);
            if (value.Equals(Fresh.Value))
            {
                return new Fresh();
            }
            else if (value.Equals(Failed.Value))
            {
                return Failed.readXml(xr);
            }
            else
            {
                throw new Exception("Invalid disposition value "+value);
            }
        }

    }

    class Stale : Disposition
    {
        public const string Value = "Stale";
        public override string ToString()
        {
            return Value;
        }
    }

    class Fresh : Disposition
    {
        public const string Value = "Fresh";
        public override string ToString()
        {
            return Value;
        }
    }

    class Failed : Disposition
    {
        //- NB Failed represents a PERMANENT failure. Any non-Stale disposition is recorded
        //- permanently in the build cache (including the globally-shared build cache!),
        //- preventing that particular verb from ever being tried again. Only record a
        //- Failed disposition if repeating the verb is guaranteed to fail again the same way.
        List<string> messages;
        public Failed(string msg = null)
        {
            messages = new List<string>();
            if (msg != null)
            {
                AddError(msg);
            }
        }
        public Failed(IEnumerable<string> messages)
        {
            this.messages = new List<string>(messages);
        }
        public void AddError(string msg)
        {
            messages.Add(msg);
        }
        public const string Value = "Failed";
        public override string ToString()
        {
            return Value;
        }
        public override IEnumerable<string> getMessages()
        {
            return messages;
        }

        const string _xml_MessageTag = "Message";

        public static new Disposition readXml(XmlReader xr)
        {
            List<string> messages = new List<string>();
            if (!xr.IsEmptyElement)
            {
                while (xr.Read())
                {
                    if (xr.NodeType == XmlNodeType.Element)
                    {
                        if (xr.Name.Equals(_xml_MessageTag))
                        {
                            messages.Add(xr.ReadElementContentAsString());
                        }
                        else
                        {
                            throw new Exception("Unrecognized Disposition::Failed tag " + xr.Name);
                        }
                    }
                    else if (xr.NodeType == XmlNodeType.EndElement)
                    {
                        Util.Assert(xr.Name.Equals(_xml_tag));
                        break;
                    }
                }
            }
            Failed f = new Failed();
            f.messages = messages;
            return f;
        }

        protected override void writeXmlExtend(XmlWriter xw)
        {
            foreach (string message in messages)
            {
                xw.WriteStartElement(_xml_MessageTag);
                xw.WriteString(message);
                xw.WriteEndElement();
            }
        }

    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml;
using System.Diagnostics;

namespace NuBuild
{
    class VerificationMessage
    {
        string _sourceLabel;
        string _message;
        public string sourceLabel { get { return _sourceLabel; } }
        public string message { get { return _message; } }

        public VerificationMessage(string sourceLabel, string message)
        {
            this._sourceLabel = sourceLabel;
            this._message = message;
        }

        public const string _xml_tag = "VerificationMessage";
        const string _xml_message_sourcefile_attr = "SourceFile";

        public void writeXml(XmlWriter xw)
        {
            xw.WriteStartElement(_xml_tag);
            xw.WriteAttributeString(_xml_message_sourcefile_attr, _sourceLabel);
            xw.WriteString(_message);
            xw.WriteEndElement();
        }

        public static VerificationMessage readXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(_xml_tag));
            string relSourcePath = xr.GetAttribute(_xml_message_sourcefile_attr);
            string message = xr.ReadElementContentAsString();
            return new VerificationMessage(relSourcePath, message);
        }
    }
}

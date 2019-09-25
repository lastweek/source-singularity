using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml;
using System.Diagnostics;

namespace NuBuild
{
    class BuildObjectValuePointer
    {
        private string _objectHash;
        public string objectHash { get { return _objectHash; } }
        
        private string _relativePath;
        //- Path relative to buildRoot/nuobj
        public string relativePath { get { return _relativePath; } }

        public BuildObjectValuePointer(string objectHash, string relativePath)
        {
            this._objectHash = objectHash;
            this._relativePath = relativePath;
        }

        public const string _xml_tag = "BuildObjectValuePointer";
        const string _xml_ObjectHash_attr = "ObjectHash";
        const string _xml_RelativePath_attr = "RelativePath";

        public void writeXml(XmlWriter xw)
        {
            xw.WriteStartElement(_xml_tag);
            xw.WriteAttributeString(_xml_ObjectHash_attr, _objectHash);
            xw.WriteAttributeString(_xml_RelativePath_attr, _relativePath);
            xw.WriteEndElement();
        }

        public static BuildObjectValuePointer readXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(_xml_tag));
            string objectHash = xr.GetAttribute(_xml_ObjectHash_attr);
            string relativePath = xr.GetAttribute(_xml_RelativePath_attr);
            return new BuildObjectValuePointer(objectHash, relativePath);
        }
    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class ResultSummaryRecord
    {
        private IVerb _verb;

        private Disposition _disposition;

        private bool _isVerificationTimeout;
        public bool isVerificationTimeout { get { return _isVerificationTimeout; } }

        public Disposition disposition { get { return _disposition; }}
        private List<BuildObjectValuePointer> _outputs;
        public IEnumerable<BuildObjectValuePointer> outputs { get { return _outputs; } }

        public ResultSummaryRecord(
            IVerb verb,
            Disposition disposition,
            IEnumerable<BuildObjectValuePointer> outputs)
        {
            bool isVerificationTimeout = false;
            if (verb!=null && verb is IRejectable)
            {
                isVerificationTimeout = ((IRejectable)verb).resultWasVerificationTimeout();
            }
            Init(verb, disposition, outputs, isVerificationTimeout);
        }

        public ResultSummaryRecord(
            Disposition disposition,
            IEnumerable<BuildObjectValuePointer> outputs,
            bool isVerificationTimeout)
        {
            Init(null, disposition, outputs, isVerificationTimeout);
        }


        private void Init(
            IVerb verb,
            Disposition disposition,
            IEnumerable<BuildObjectValuePointer> outputs,
            bool isVerificationTimeout)

        {
            this._verb = verb;
            this._disposition = disposition;
            this._outputs = new List<BuildObjectValuePointer>(outputs);
            this._isVerificationTimeout = isVerificationTimeout;
            if (_verb is IRejectable)
            {
                _isVerificationTimeout = ((IRejectable)_verb).resultWasVerificationTimeout();
            }
        }

        public const string _xml_tag = "ResultSummaryRecord";
        public const string _IsVerificationTimeout_attr = "IsVerificationTimeout";

        public string toXml()
        {
            StringBuilder sb = new StringBuilder();
            XmlWriterSettings settings = new XmlWriterSettings();
            settings.Indent = true;
            XmlWriter xw = XmlWriter.Create(sb, settings);
            xw.WriteStartDocument();
            writeXml(xw);
            xw.Close();
            return sb.ToString();
        }

        public void writeXml(XmlWriter xw)
        {
            xw.WriteStartElement(_xml_tag);
            xw.WriteAttributeString(
                _IsVerificationTimeout_attr, _isVerificationTimeout.ToString());
            if (_verb != null)
            {
                _verb.writeTimingXml(xw);
                _verb.writeDebugXml(xw);
            }
            _disposition.writeXml(xw);
            foreach (BuildObjectValuePointer bovp in _outputs)
            {
                bovp.writeXml(xw);
            }
            xw.WriteEndElement();
        }

        static public ResultSummaryRecord fromXml(string xs)
        {
            XmlReader xr = XmlReader.Create(new StringReader(xs));
            while (xr.Read())
            {
                if (xr.NodeType == XmlNodeType.Element)
                {
                    break;
                }
            }
            return readXml(xr);
        }

        static public ResultSummaryRecord readXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(_xml_tag));

            bool isVerificationTimeout = false;
            Boolean.TryParse(
                xr.GetAttribute(_IsVerificationTimeout_attr), out isVerificationTimeout);

            xr.ReadToFollowing(Disposition._xml_tag);
            Disposition d = Disposition.readXml(xr);

            List<BuildObjectValuePointer> lbovp = new List<BuildObjectValuePointer>();
            while (xr.Read())
            {
                if (xr.NodeType == XmlNodeType.EndElement)
                {
                    Util.Assert(xr.Name.Equals(_xml_tag));
                    break;
                }
                else if (xr.NodeType == XmlNodeType.Element)
                {
                    if (xr.Name.Equals(BuildObjectValuePointer._xml_tag))
                    {
                        lbovp.Add(BuildObjectValuePointer.readXml(xr));
                    }
                    else
                    {
                        throw new Exception("Unknown xml tag " + xr.Name);
                    }
                }
            }
            return new ResultSummaryRecord(d, lbovp, isVerificationTimeout);
        }

    }
}

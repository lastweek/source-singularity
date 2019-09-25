using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Xml;
using System.Text.RegularExpressions;

namespace NuBuild
{

    class VerificationResult
    {
        string _sourceLabel;
        bool _pass;
        double _cpuTime;
        int _parseFailures;
        int _verificationFailures;
        int _timeouts;
        List<VerificationMessage> messages;
        Presentation _presentation;

        public string sourceLabel { get { return _sourceLabel; } }
        public bool pass { get { return _pass; } }
        public double cpuTime { get { return _cpuTime; } }
        public int parseFailures { get { return _parseFailures; } }
        public int verificationFailures { get { return _verificationFailures; } }
        public int timeouts { get { return _timeouts; } }
        public Presentation presentation { get { return _presentation; } }

        public IEnumerable<VerificationMessage> getMessages() { return messages; }
        static Regex whitespace = new Regex("^\\s*$");

        public VerificationResult(string sourceLabel, ProcessInvoker pinv, IVerificationResultParser parser)
        {
            _sourceLabel = sourceLabel;
            _cpuTime = pinv.cpuTime;
            messages = new List<VerificationMessage>();

            string stdout = pinv.getStdout();
            if (!whitespace.Match(stdout).Success)
            {
                messages.Add(new VerificationMessage(sourceLabel, stdout));
            }
            string stderr = pinv.getStderr();
            if (!whitespace.Match(stderr).Success)
            {
                messages.Add(new VerificationMessage(sourceLabel, stderr));
            }

            _parseFailures = 0;
            _verificationFailures = 0;
            _timeouts = 0;
            parser.parseOutput(stdout + stderr, out _parseFailures, out _verificationFailures, out _timeouts);
            _pass = _parseFailures == 0 && _verificationFailures == 0 && _timeouts == 0;
        }

        public void addXmlFiller(Presentation presentation)
        {
            this._presentation = presentation;
        }

        public VerificationResult(string sourceLabel, bool pass, double cpuTime, int parseFailures, int verificationFailures, int timeouts, IEnumerable<VerificationMessage> messages)
        {
            this._sourceLabel = sourceLabel;
            this._pass = pass;
            this._cpuTime = cpuTime;
            this._parseFailures = parseFailures;
            this._verificationFailures = verificationFailures;
            this._timeouts = timeouts;
            this.messages = new List<VerificationMessage>(messages);
        }

        private VerificationResult()
        {
        }

        const string PASS = "pass";
        const string FAIL = "fail";

        public void toXmlFile(string path)
        {
            File.Delete(path);
            using (FileStream s = File.OpenWrite(path))
            {
                XmlWriterSettings settings = new XmlWriterSettings();
                settings.Indent = true;
                XmlWriter xw = XmlWriter.Create(s, settings);
                xw.WriteStartDocument();
                writeXml(xw);
                xw.Close();
            }
        }

        public static VerificationResult fromXmlFile(string path)
        {
            using (Stream ins = File.OpenRead(path))
            {
                XmlReader xr = XmlReader.Create(ins);
                while (xr.Read())
                {
                    if (xr.NodeType == XmlNodeType.Element)
                    {
                        break;
                    }
                }
                return readXml(xr);
            }
        }

        public const string _xml_tag = "VerificationResult";
        const string _xml_sourcePath_attr = "SourcePath";
        const string _xml_outcome_attr = "Outcome";
        const string _xml_parseFailures_attr = "ParseFailures";
        const string _xml_verificationFailures_attr = "VerificationFailures";
        const string _xml_timeouts_attr = "Timeouts";
        const string _xml_cputime_attr = "CPUTime";
        const string _xml_message_tag = "Message";
        const string _xml_message_sourcefile_attr = "SourceFile";

        public void writeXml(XmlWriter xw)
        {
            xw.WriteStartElement(_xml_tag);
            xw.WriteAttributeString(_xml_sourcePath_attr, _sourceLabel);
            xw.WriteAttributeString(_xml_outcome_attr, _pass ? PASS : FAIL);
            xw.WriteAttributeString(_xml_cputime_attr, _cpuTime.ToString());
            xw.WriteAttributeString(_xml_parseFailures_attr, _parseFailures.ToString());
            xw.WriteAttributeString(_xml_verificationFailures_attr, _verificationFailures.ToString());
            xw.WriteAttributeString(_xml_timeouts_attr, _timeouts.ToString());
            foreach (VerificationMessage message in messages)
            {
                message.writeXml(xw);
            }
            if (_presentation!=null)
            {
                _presentation.fillXml(xw);  //- TODO we don't know yet how to parse this stuff back in.
            }
            xw.WriteEndElement();
        }

        public void addBasicPresentation()
        {
            PresentationBuilder pr = new PresentationBuilder();

            int any_failures = parseFailures + verificationFailures + timeouts;
            string overall_status = any_failures > 0 ? "Fail" : "Success";

            pr.pre("Git info goes here.\n");
            pr.spacer();
            pr.startHeader();
            pr.color(any_failures==0 ? Presentation.GREEN : Presentation.RED, "Overall status: " + overall_status);
            pr.endHeader();
            pr.line(String.Format("{0} parse failures, {1} verification failures, {2} timeouts",
                _parseFailures, _verificationFailures, _timeouts));
            pr.spacer();

            foreach (VerificationMessage message in messages)
            {
                pr.pre(message.message);
            }
            Presentation pres = pr.fix();

            addXmlFiller(pres);
        }

        public static VerificationResult readXml(XmlReader xr)
        {
            Util.Assert(xr.Name.Equals(_xml_tag));
            VerificationResult rc = new VerificationResult();
            rc._sourceLabel = xr.GetAttribute(_xml_sourcePath_attr);
            string outcome = xr.GetAttribute(_xml_outcome_attr);
            if (outcome.Equals(PASS))
            {
                rc._pass = true;
            }
            else if (outcome.Equals(FAIL))
            {
                rc._pass = false;
            }
            else
            {
                throw new Exception("Invalid outcome value " + outcome);
            }
            rc._cpuTime = Double.Parse(xr.GetAttribute(_xml_cputime_attr));
            rc._parseFailures = Int32.Parse(xr.GetAttribute(_xml_parseFailures_attr));
            rc._verificationFailures = Int32.Parse(xr.GetAttribute(_xml_verificationFailures_attr));
            rc._timeouts = Int32.Parse(xr.GetAttribute(_xml_timeouts_attr));
            rc.messages = new List<VerificationMessage>();

            while (xr.Read())
            {
                if (xr.NodeType == XmlNodeType.EndElement)
                {
                    Util.Assert(xr.Name.Equals(_xml_tag));
                    break;
                }
                else if (xr.NodeType == XmlNodeType.Element)
                {
                    if (xr.Name.Equals(VerificationMessage._xml_tag))
                    {
                        rc.messages.Add(VerificationMessage.readXml(xr));
                    }
                    else if (xr.Name.Equals(Presentation._xml_tag))
                    {
                        rc._presentation = Presentation.fromXml(xr.ReadSubtree());
                    }
                    else
                    {
                        throw new Exception("Unknown xml tag " + xr.Name);
                    }
                }
            }
            return rc;
        }

        internal bool wasOnlyTimeouts()
        {
            return verificationFailures==0 && timeouts > 0;
        }
    }
}

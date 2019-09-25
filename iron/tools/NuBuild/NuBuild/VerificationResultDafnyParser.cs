using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Text.RegularExpressions;

namespace NuBuild
{
    class VerificationResultDafnyParser : IVerificationResultParser
    {
        static Regex disposition_timeouts_re = new Regex("Dafny program verifier finished with (\\d*) verified, (\\d*) errors*, (\\d) time outs*");
        static Regex disposition_notimeouts_re = new Regex("Dafny program verifier finished with (\\d*) verified, (\\d*) errors*");
        static Regex disposition_parse_error_re = new Regex("Error opening file");
        static Regex disposition_parse_error2_re = new Regex("(\\d*) parse errors detected in");
        static Regex disposition_parse_error3_re = new Regex("(\\d*) resolution/type errors detected in");
        static Regex disposition_proverdied_re = new Regex("Prover error: Prover died");

        public void parseOutput(string s, out int _parseFailures, out int _verificationFailures, out int _timeouts)
        {
            _parseFailures = 0;
            _verificationFailures = 0;
            _timeouts = 0;
            Match m = disposition_timeouts_re.Match(s);
            if (m.Success)
            {
                //-int succeeding_methods = Int32.Parse(m.Groups[1].ToString());
                _verificationFailures = Int32.Parse(m.Groups[2].ToString());
                _timeouts = Int32.Parse(m.Groups[3].ToString());
                return;
            }
            m = disposition_notimeouts_re.Match(s);
            if (m.Success)
            {
                //-int succeeding_methods = Int32.Parse(m.Groups[1].ToString());
                _verificationFailures = Int32.Parse(m.Groups[2].ToString());
                return;
            }
            m = disposition_parse_error_re.Match(s);
            if (m.Success)
            {
                _parseFailures = 1;
                return;
            }
            m = disposition_parse_error2_re.Match(s);
            if (m.Success)
            {
                _parseFailures = Int32.Parse(m.Groups[1].ToString());
                return;
            }
            m = disposition_parse_error3_re.Match(s);
            if (m.Success)
            {
                _parseFailures = Int32.Parse(m.Groups[1].ToString());
                return;
            }
            m = disposition_proverdied_re.Match(s);
            if (m.Success)
            {
                _parseFailures = 1;
                return;
            }
            _parseFailures = 1;
            Logger.WriteLine("NuBuild WARNING: unexpected Dafny error message; lumping into parse errors.");
            //-throw new Exception("Unable to parse Dafny output");
        }
    }
}

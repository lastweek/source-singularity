using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    interface IVerificationResultParser
    {
        void parseOutput(string s,
            out int _parseFailures, out int _verificationFailures, out int _timeouts);
    }
}

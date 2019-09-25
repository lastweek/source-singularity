using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class VerificationRequest
    {

        public enum VerifyMode { Verify, NoSymDiff, SelectiveVerify, NoVerify };

        public VerifyMode verifyMode;
        public List<string> selectiveVerifyModuleNames;

        public VerificationRequest()
        {
            verifyMode = VerifyMode.Verify;
            selectiveVerifyModuleNames = new List<string>();
        }

        public bool isComplete()
        {
            return verifyMode == VerifyMode.Verify;
        }

        public override string ToString()
        {
            if (verifyMode == VerifyMode.SelectiveVerify)
            {
                return verifyMode.ToString() + "(" + String.Join(",", selectiveVerifyModuleNames) + ")";
            }
            else
            {
                return verifyMode.ToString();
            }
        }

        public enum SymDiffMode { UseSymDiff, NoSymDiff };
        public SymDiffMode getSymDiffMode()
        {
            return verifyMode == VerifyMode.Verify ? SymDiffMode.UseSymDiff : SymDiffMode.NoSymDiff;
        }
    }
}

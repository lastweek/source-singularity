using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class VerificationObligationList
    {
        public const string VOL_EXTN = ".vol";  //- VOL = Verification Object List

        private readonly List<BuildObject> _verificationObligations;
        private bool _fixed;

        public VerificationObligationList()
        {
            _verificationObligations = new List<BuildObject>();
        }

        public VerificationObligationList(IEnumerable<BuildObject> data)
        {
            _verificationObligations = new List<BuildObject>(data);
            _fixed = true;
        }

        public void Add(BuildObject obj)
        {
            Util.Assert(!_fixed);
            _verificationObligations.Add(obj);
        }

        public IEnumerable<BuildObject> getVerificationObligations()
        {
            Util.Assert(_fixed);
            return _verificationObligations;
        }

        public static VerificationObligationList fetch(BuildObject obj)
        {
            VerificationObligationList vol = new VerificationObligationList();
            using (TextReader sr = BuildEngine.theEngine.getNuObjContents().openRead(obj))
            {
                string line;
                while ((line = sr.ReadLine()) != null)
                {
                    Util.Assert(!line.StartsWith(BuildEngine.theEngine.getSrcRoot()));   //- unimplemented
                    Util.Assert(!line.StartsWith(BuildEngine.theEngine.getVirtualRoot()));   //- nonsense
                    vol.Add(new BuildObject(line));
                }
            }
            vol._fixed = true;
            return vol;
        }

        public void store(BuildObject obj)
        {
            _fixed = true;
            string[] lines = _verificationObligations.Select(vo => vo.getRelativePath()).ToArray();
            File.WriteAllLines(obj.getFilesystemPath(), lines);
        }
    }
}

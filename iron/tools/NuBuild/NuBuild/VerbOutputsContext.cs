using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class VerbOutputsContext
        : IncludePathContext
    {
        IVerb sourceVerb;
        string descr;
        HashSet<BuildObject> _dafnyOutputs;
        bool _assertSuspiciousDafnyImpls;

        public VerbOutputsContext(IVerb sourceVerb, bool assertSuspiciousDafnyImpls)
        {
            this.sourceVerb = sourceVerb;
            this.descr = "VerbOutputs(" + sourceVerb + ")";
            this._assertSuspiciousDafnyImpls = assertSuspiciousDafnyImpls;
        }

        public override string ToString()
        {
            return descr;
        }

        private HashSet<BuildObject> dafnyOutputs
        {
            get
            {
                if (_dafnyOutputs == null)
                {
                    _dafnyOutputs = new HashSet<BuildObject>(sourceVerb.getOutputs());
                }
                return _dafnyOutputs;
            }
        }


        public override BuildObject search(string basename, ModPart modPart)
        {

            //- Kinda linear
            //-Logger.WriteLine("Looking for " + basename);
            foreach (BuildObject obj in dafnyOutputs)
            {
                if (BeatExtensions.whichPart(obj) != modPart)
                {
                    continue;
                }
                //-Logger.WriteLine("  trying " + obj.getFileNameWithoutExtension() + " from " + obj);
                if (String.Equals(obj.getFileNameWithoutExtension(), basename, StringComparison.OrdinalIgnoreCase))
                {
                    if (_assertSuspiciousDafnyImpls)
                    {
                        DafnyCCVerb.AssertSmellsImplementy(obj);
                    }
                    return obj;
                }
            }
            return null;
        }
    }
}

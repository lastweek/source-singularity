using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class BoogieAsmLinkVerb
            : BoogieAsmWorkerBase, IAsmProducer
    {
        protected override int getVersion() { return 23; }
        protected override string getAction() { return "-link"; }
        protected override bool outFlagWorks() { return false; }
        protected override bool includeAllImps() { return true; }

        public BuildObject getAsmFile() {
            return basmInput.makeOutputObject(MasmVerb.MASM_EXTN);
        }

        public override BuildObject outputFile()
        {
            return getAsmFile();
        }

        public BoogieAsmLinkVerb(IContextGeneratingVerb context, BuildObject input)
            : base(context, input)
        {
        }


        public override IEnumerable<IVerb> getVerbs()
        {
            
            
            return getVerifyishVerbs();
        }

    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class SymDiffMergeVerb : SymDiffMergeBaseVerb, IProcessInvokeAsyncVerb
    {    
        const int version = 2;
        public const string MERGED_EXTN = ".merge";

        //- TODO: Run in a custom directory!
        AbstractId abstractId;
        BoogieAsmVerifyVerb basmVerb;
        BuildObject mutualSummary;
        SymDiffCombineVerb combiner;
        BuildObject output;

        public SymDiffMergeVerb(BoogieAsmVerifyVerb basmVerb, SymDiffCombineVerb combiner)
        {
            this.basmVerb = basmVerb;
            this.mutualSummary = basmVerb.getMutualSummary();
            this.combiner = combiner;

            abstractId = new AbstractId(this.GetType().Name, version, combiner.getOutputFile().ToString()); //- String.Format("{0},{1}", One should suffice for uniqueness: mutualSummary, combiner.getOutputFile()));
            output = this.basmVerb.outputFile().makeOutputObject(MERGED_EXTN + BoogieVerb.BPL_EXTN);
            
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        protected override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() { mutualSummary, combiner.getOutputFile() };
        }

        public override BuildObject getOutputFile()
        {
            return output;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return base.getVerbs().Concat(new List<IVerb>() { basmVerb, combiner });
        }

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-merge");
            args.Add(mutualSummary.getRelativePath());
            args.Add(combiner.getOutputFile().getRelativePath());
            return args;
        }
       
    }
}

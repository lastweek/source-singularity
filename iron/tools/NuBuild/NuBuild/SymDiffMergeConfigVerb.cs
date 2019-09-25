using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class SymDiffMergeConfigVerb : SymDiffMergeBaseVerb, IProcessInvokeAsyncVerb
    {    
        const int version = 2;
        public const string CONFIG_EXTN = ".config";

        //- TODO: Run in a custom directory!
        AbstractId abstractId;
        BoogieAsmVerifyVerb basmVerb;
        BuildObject mutualSummary;
        SymDiffInferVerb inferVerb;
        BuildObject inferredConfig;
        BuildObject output;


        public SymDiffMergeConfigVerb(BoogieAsmVerifyVerb basmVerb, SymDiffInferVerb inferVerb)
        {
            this.basmVerb = basmVerb;
            this.mutualSummary = basmVerb.getMutualSummary();
            this.inferVerb = inferVerb;
            this.inferredConfig = inferVerb.getOutputFile();

            abstractId = new AbstractId(this.GetType().Name, version, inferredConfig.ToString());  //- One should suffice for uniqueness: String.Format("{0},{1}", mutualSummary,inferredConfig));
            output = this.basmVerb.outputFile().makeOutputObject(CONFIG_EXTN);
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        protected override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() { mutualSummary, inferredConfig };
        }

        public override BuildObject getOutputFile()
        {
            return output;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return base.getVerbs().Concat(new List<IVerb>() { basmVerb, inferVerb });
        }

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-config");
            args.Add(mutualSummary.getRelativePath());
            args.Add(inferredConfig.getRelativePath());
            return args;
        }
       
    }
}

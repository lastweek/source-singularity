using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class SymDiffEngine
    {        
        public static void BuildPipeline(IContextGeneratingVerb context, BuildObject input, out BuildObject bplFile, out IVerb workerVerb)
        {
            BoogieAsmVerifyVerb basmVerb = new BoogieAsmVerifyVerb(context, input, true);
            SymDiffExtractVerb left  = new SymDiffExtractVerb(basmVerb, SymDiffExtractVerb.Mode.LEFT);
            SymDiffExtractVerb right = new SymDiffExtractVerb(basmVerb, SymDiffExtractVerb.Mode.RIGHT);
            SymDiffInferVerb infer = new SymDiffInferVerb(left, right);
            SymDiffMergeConfigVerb mergeConfig = new SymDiffMergeConfigVerb(basmVerb, infer);
            SymDiffCombineVerb combiner = new SymDiffCombineVerb(left, right, mergeConfig);
            SymDiffMergeVerb merger = new SymDiffMergeVerb(basmVerb, combiner);

            bplFile = merger.getOutputFile();
            workerVerb = merger;
        }     
    }
}

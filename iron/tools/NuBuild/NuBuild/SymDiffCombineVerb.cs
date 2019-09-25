using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class SymDiffCombineVerb : SymDiffBaseVerb, IProcessInvokeAsyncVerb
    { 
        public const string MERGED_FILE_NAME = "mergedProgSingle.bpl";

        const int version = 2;
        
        AbstractId abstractId;
        SymDiffExtractVerb left;
        SymDiffExtractVerb right;
        SymDiffMergeConfigVerb merger;

        BuildObject outputFile;

        public SymDiffCombineVerb(SymDiffExtractVerb left, SymDiffExtractVerb right, SymDiffMergeConfigVerb merger)
        {
            this.left = left;
            this.right = right;
            this.merger = merger;

            abstractId = new AbstractId(this.GetType().Name, version, left.getOutputFile().ToString());      //- Naming one of the files should be sufficient to uniquely identify the combiner






            outputFile = mkOutputFile();
        }

        private BuildObject mkOutputFile() 
        {
            //- SymDiff always uses the same file name in the working directory
            return new BuildObject(Path.Combine(left.getOutputFile().getDirPath(), MERGED_FILE_NAME));
        }

        public override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() { left.getOutputFile(), right.getOutputFile(), merger.getOutputFile() };
        }

        public override BuildObject getOutputFile()
        {
            return outputFile;
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        protected override string getWorkingDir() 
        {
            return outputFile.getAbsoluteDirPath();
        }
    
        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { left, right, merger };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { getOutputFile() };
        }

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-allInOne");
            args.Add(left.getOutputFile().getFileName());
            args.Add(right.getOutputFile().getFileName());
            args.Add(merger.getOutputFile().getFileName());
            //-args.Add(left.getOutputFile().getRelativePath());
            //-args.Add(right.getOutputFile().getRelativePath());
            //-args.Add(merger.getOutputFile().getRelativePath());

            List<string> extra_args = new List<string>() { "-asserts", "-freeContracts", "-usemutual", "-sound", "-dontUseHoudiniForMS", "-checkMutualPrecondNonTerminating" };
            args.AddRange(extra_args);

            return args;
        }       
    }
}

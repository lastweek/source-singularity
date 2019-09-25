using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class SymDiffInferVerb : SymDiffBaseVerb, IProcessInvokeAsyncVerb
    { 
        public const string CONFIG = ".partial_config";

        const int version = 2;
        
        AbstractId abstractId;
        SymDiffExtractVerb left;
        SymDiffExtractVerb right;

        public SymDiffInferVerb(SymDiffExtractVerb left, SymDiffExtractVerb right)
        {
            this.left = left;
            this.right = right;

            abstractId = new AbstractId(this.GetType().Name, version, left.getOutputFile().ToString().ToString());      //- Left should suffice to uniquely ID
            
        }

        public override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() { left.getOutputFile(), right.getOutputFile() };
        }

        public override BuildObject getOutputFile()
        {
            //- Choice of left/right doesn't matter here, since we're dropping the extension
            return left.getOutputFile().makeOutputObject(CONFIG);   
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }
    
        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { left, right };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { getOutputFile() };
        }

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-inferConfig");
            args.Add(left.getOutputFile().getRelativePath());
            args.Add(right.getOutputFile().getRelativePath());

            return args;
        }       

        public override Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            if (!(worker.pinv.disposition is Failed))
            {
                File.WriteAllText(getOutputFile().getFilesystemPath(), worker.pinv.getStdout());
            }
            return worker.pinv.disposition;
        }
    }
}

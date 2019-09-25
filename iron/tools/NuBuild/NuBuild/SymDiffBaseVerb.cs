using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    abstract class SymDiffBaseVerb : Verb, IProcessInvokeAsyncVerb
    {    
        const int version = 2;

        //- TODO: Run in a custom directory!

        public abstract IEnumerable<BuildObject> getInputFiles();
        public abstract BuildObject getOutputFile();

        protected abstract List<string> getArgs();

        protected virtual string getWorkingDir() { return null; }

        protected static SourcePath getSymDiffExecutable()
        {
            return new SourcePath("tools/SymDiff/SymDiff.exe", SourcePath.SourceType.sourceTypeTools);
        }


        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            IEnumerable<BuildObject> deps = getInputFiles();
            deps.Union(new List<BuildObject>() { getSymDiffExecutable() });
            return deps;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { getOutputFile() };
        }
    

        public override IVerbWorker getWorker()
        {
            List<string> args = getArgs();
     
            return new ProcessInvokeAsyncWorker(this,
                getSymDiffExecutable().getRelativePath(), args.ToArray(), ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE, getDiagnosticsBase(), workingDir:getWorkingDir());            
        }

        public virtual Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            return worker.pinv.disposition;
        }
    }
}

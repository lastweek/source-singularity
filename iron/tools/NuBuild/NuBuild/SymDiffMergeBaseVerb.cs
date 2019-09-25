using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    abstract class SymDiffMergeBaseVerb : Verb, IProcessInvokeAsyncVerb
    {    
        const int version = 2;

        //- TODO: Run in a custom directory!

        protected abstract IEnumerable<BuildObject> getInputFiles();
        public abstract BuildObject getOutputFile();

        protected abstract List<string> getArgs();

        static NmakeVerb boogieAsmBuildExecutableVerb = new NmakeVerb(new SourcePath("tools/BoogieAsm/makefile", SourcePath.SourceType.sourceTypeTools));

        static BuildObject getSymDiffMergeExecutable()
        {
            return new BuildObject(Path.Combine(boogieAsmBuildExecutableVerb.getOutputPath().getRelativePath(), "symdiffmerge.exe"));
        }


        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;

            IEnumerable<BuildObject> deps = getInputFiles();
            deps.Union(new List<BuildObject>() { getSymDiffMergeExecutable() });

            return deps;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new [] { boogieAsmBuildExecutableVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { getOutputFile() };
        }
    

        public override IVerbWorker getWorker()
        {
            List<string> args = getArgs();
     
            return new ProcessInvokeAsyncWorker(this,
                getSymDiffMergeExecutable().getRelativePath(), args.ToArray(), ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE, getDiagnosticsBase());            
        }

        public virtual Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            if (!(worker.pinv.disposition is Failed))
            {
                File.WriteAllText(getOutputFile().getFilesystemPath(), worker.pinv.getStdout());
            }
            return worker.pinv.disposition;
        }
    }
}

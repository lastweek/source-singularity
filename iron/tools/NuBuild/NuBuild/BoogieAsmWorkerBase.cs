using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    abstract class BoogieAsmWorkerBase
        : BoogieAsmDepBase, IProcessInvokeAsyncVerb
    {
        protected abstract string getAction();
        protected abstract bool outFlagWorks(); //- Weird that it works for -verify but not -link!
        protected virtual void extendArgs(List<string> args) { }
        protected virtual void postprocess() { }
      
        public BoogieAsmWorkerBase(IContextGeneratingVerb context, BuildObject input)
            : base(context, input)
        { }

        public override IVerbWorker getWorker()
        {
            List<string> args = new List<string>();
            //- args.add(BUILD_DEFS
            //- args.add(boogieasm_flags)
            args.Add(getAction());
            string finalStdoutPath = null;
            if (outFlagWorks())
            {
                args.Add("-out");
                args.Add(outputFile().getRelativePath());
            }
            else
            {
                finalStdoutPath = outputFile().getFilesystemPath();
            }

            BasmModuleAccumulator acc = new BasmModuleAccumulator(context, upstreamObj, includeAllImps());
            Util.Assert(acc.ddisp == DependencyDisposition.Complete);
            args.AddRange(acc.basmModules.Select(module => module.getRelativePath()));
            args.AddRange(context.getPoundDefines().ToDefArgs());
            extendArgs(args);

            return new ProcessInvokeAsyncWorker(this,
                    getBoogieasmExecutable().getRelativePath(),
                    args.ToArray(),
                    ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE,
                    getDiagnosticsBase(),
                    finalStdoutPath: finalStdoutPath);
        }

        public Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            postprocess();
            return worker.pinv.disposition;
        }

    }
}

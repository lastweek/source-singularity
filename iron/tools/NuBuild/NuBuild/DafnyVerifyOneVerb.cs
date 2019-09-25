using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;
using System.IO;

namespace NuBuild
{
    class DafnyVerifyOneVerb
        : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        public const string DAFNY_EXTN = ".dfy";
        const int version = 8;

        SourcePath dfysource;
        AbstractId abstractId;
        static SourcePath _dafnyExecutable;
        static SourcePath getDafnyExecutable()
        {
            //- TODO this should eventually be a BuildObject from *building* the executable.
            if (_dafnyExecutable == null)
            {
                _dafnyExecutable = new SourcePath("tools/Dafny/Dafny.exe", SourcePath.SourceType.sourceTypeTools);
            }
            return _dafnyExecutable;
        }

        public DafnyVerifyOneVerb(SourcePath dfysource)
        {
            this.dfysource = dfysource;
            this.abstractId = new AbstractId(this.GetType().Name, version, dfysource.ToString());                
        }

        public override AbstractId getAbstractIdentifier()
        {
            return abstractId;
        }

        protected override BuildObject getSource() { return dfysource; }

        TransitiveDepsVerb getTransitiveDepsVerb()
        {
            return new DafnyTransitiveDepsVerb(dfysource);
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            TransitiveDepsVerb depsVerb = getTransitiveDepsVerb();
            HashSet<BuildObject> result = depsVerb.getAvailableDeps(out ddisp);
            result.Add(getDafnyExecutable());
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[0];    //- All inputs are sources
        }

        public override BuildObject getOutputFile()
        {
            return dfysource.makeOutputObject(".dfy.v");
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new[] { getOutputFile() };
        }

        const string ADDDAFNYFLAG_LABEL = "AddDafnyFlag";
        public override IVerbWorker getWorker()
        {
            List<string> arguments = new List<string>();
            arguments.Add("/dafnycc");
            arguments.Add("/z3opt:ARITH_RANDOM_SEED=1");
            arguments.Add("/compile:0");
            arguments.Add("/timeLimit:30");
            arguments.Add("/noCheating:1");
            foreach (string[] ann in new AnnotationScanner(dfysource).getAnnotations(ADDDAFNYFLAG_LABEL))
            {
                if (ann.Length!=2) {
                    throw new SourceConfigurationError("Expected exactly 1 argument to " + ADDDAFNYFLAG_LABEL);
                }
                arguments.Add(ann[1]);
            }
            arguments.Add(dfysource.getRelativePath());
            

            return new ProcessInvokeAsyncWorker(this,
                getDafnyExecutable().getRelativePath(),
                arguments.ToArray(),
                ProcessInvoker.RcHandling.NONZERO_RC_IS_OKAY,
                getDiagnosticsBase());
        }

        public Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            VerificationResult vr = new VerificationResult(dfysource.getRelativePath(), worker.pinv, new VerificationResultDafnyParser());
            vr.addBasicPresentation();
            vr.toXmlFile(getOutputFile().getRelativePath());
            setWasVerificationTimeout(vr.wasOnlyTimeouts());
            return worker.pinv.disposition;
        }

        public IEnumerable<BuildObject> getDirectIncludes()
        {
            //- By the time this method is called by VerbToposorter,
            //- this verb is scheduled for execution, and hence its deps
            //- are complete. So all of these lookups should succeed.
            //- (wait, does that follow?)
            return getTransitiveDepsVerb().getShallowIncludes();
        }

    }
}

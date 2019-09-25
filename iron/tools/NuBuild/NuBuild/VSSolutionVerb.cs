using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class VSSolutionVerb
        : Verb, IProcessInvokeAsyncVerb
    {
        private const int version = 2;
        private SourcePath _solutionFile;
        private AbstractId _abstractId;
        private VSSolutionParser _solutionParser;
        private string _outputPath;
        private string _outputPathSuffix;

        public VSSolutionVerb(SourcePath solutionFile)
        {
            _solutionFile = solutionFile;
            _abstractId = new AbstractId(this.GetType().Name, version, _solutionFile.ToString());

            //- Parse the solution file
            _solutionParser = new VSSolutionParser(_solutionFile);

            //- Generate output path
            _outputPath = ".";
            int depth = _solutionFile.getDirPath().Split(@"\/".ToCharArray(), StringSplitOptions.RemoveEmptyEntries).Length;
            for (int i = 0; i < depth; i++)
            {
                _outputPath = Path.Combine(_outputPath, "..");
            }

            _outputPathSuffix = Path.Combine(BuildEngine.theEngine.getObjRoot(), _solutionFile.getDirPath());
            _outputPath = Path.Combine(_outputPath, _outputPathSuffix);
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return _solutionParser.getDependencies();
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return from output in _solutionParser.getOutputs() select new BuildObject(Path.Combine(BuildEngine.theEngine.getObjRoot(), output.getRelativePath()));
        }

        public BuildObject getOutputPath()
        {
            return new BuildObject(_outputPathSuffix);
        }

        public override IVerbWorker getWorker()
        {
            List<string> args = new List<String>();

            args.Add(String.Format("/p:OutDir={0}", _outputPath));
            args.Add(_solutionFile.getFilesystemPath());

            return new ProcessInvokeAsyncWorker(this,
                    "c:/Windows/Microsoft.NET/Framework/v4.0.30319/MSBuild.exe",
                    args.ToArray(),
                    ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE,
                    failureBase: getDiagnosticsBase(),
                    allowAbsoluteExe:true,
                    allowAbsoluteArgs:true
                    );

        }
        public Disposition complete(ProcessInvokeAsyncWorker worker)
        {
              return worker.pinv.disposition;
        }

        public override AbstractId getAbstractIdentifier()
        {
            return _abstractId;
        }
    }

}


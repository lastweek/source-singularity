using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class NmakeVerb
        : Verb, IProcessInvokeAsyncVerb
    {
        private const int version = 6;
        private SourcePath _makefile;
        private CustomManifestParser _customManifest;
        private AbstractId _abstractId;
        private string _outputPath;
        private string _outputPathSuffix;

        public NmakeVerb(SourcePath makefile)
        {
            _makefile = makefile;
            _abstractId = new AbstractId(this.GetType().Name, version, _makefile.ToString());

            //- Generate output path
            _outputPath = ".";
            int depth = _makefile.getDirPath().Split(@"\/".ToCharArray(), StringSplitOptions.RemoveEmptyEntries).Length;
            for (int i = 0; i < depth; i++)
            {
                _outputPath = Path.Combine(_outputPath, "..");
            }

            _outputPathSuffix = Path.Combine(BuildEngine.theEngine.getObjRoot(), _makefile.getDirPath());
            _outputPath = Path.Combine(_outputPath, _outputPathSuffix);
            _customManifest = new CustomManifestParser(makefile);
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return _customManifest.getDependencies();
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return from output in _customManifest.getOutputs() select new BuildObject(Path.Combine(BuildEngine.theEngine.getObjRoot(), output.getRelativePath()));
        }

        public BuildObject getOutputPath()
        {
            return new BuildObject(_outputPathSuffix);
        }

        public override IVerbWorker getWorker()
        {
            List<string> args = new List<String>();

            args.Add(String.Format("OBJ={0}\\obj", _outputPath));
            args.Add(String.Format("BIN={0}", _outputPath));

            args.Add("-f");
            args.Add(_makefile.getFilesystemPath());

            return new ProcessInvokeAsyncWorker(this,
                    "c:/Program Files (x86)/Microsoft Visual Studio 12.0/VC/bin/nmake.exe",
                    args.ToArray(),
                    ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE,
                    workingDir:_makefile.getFilesystemDirPath(),
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


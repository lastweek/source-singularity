using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class AsmRewriterVerb : Verb, IProcessInvokeAsyncVerb, IAsmProducer
    {
        public const string WASM_EXTN = ".wasm";        
        const int version = 1;

        BoogieAsmLinkVerb asmVerb;
        AbstractId abstractId;
        BuildObject asmFileOut;
        BuildObject asmFileIn;
        BuildObject pythonScript;

        public AsmRewriterVerb(BoogieAsmLinkVerb asmVerb)
        {            
            this.asmVerb = asmVerb;
            this.asmFileIn = asmVerb.getAsmFile();
            this.asmFileOut = asmFileIn.makeOutputObject(WASM_EXTN);

            abstractId = new AbstractId(this.GetType().Name, version, asmFileOut.ToString());            
            this.pythonScript = new SourcePath("tools/scripts/build-standalone-asm.py", SourcePath.SourceType.sourceTypeTools);
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        public BuildObject getAsmFile() { return asmFileOut; } 
     
        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return new List<BuildObject>() { asmFileIn, pythonScript };
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { asmVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { getAsmFile() };
        }

        public override IVerbWorker getWorker()
        {
            List<string> args = new List<string>() { pythonScript.getRelativePath(), asmFileIn.getRelativePath() };
            string python_exe = @"C:\Python27\pythonw.exe";

            if (!File.Exists(python_exe))
            {
                throw new FileNotFoundException("Missing python executable: " + python_exe + ".  Try installing from: https://-www.python.org/");
            }
     
            return new ProcessInvokeAsyncWorker(this,
                python_exe, args.ToArray(), ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE, getDiagnosticsBase(), allowAbsoluteExe:true);            
        }

        public Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            if (!(worker.pinv.disposition is Failed)) {
                File.WriteAllText(asmFileOut.getFilesystemPath(), worker.pinv.getStdout());
            }

            return worker.pinv.disposition;
        }
    }
}

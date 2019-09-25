using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class MasmVerb : Verb, IProcessInvokeAsyncVerb
    {
        public const string MASM_EXTN = ".asm";
        public const string OBJ_EXTN = ".obj";
        const int version = 4;

        IAsmProducer asmVerb;
        AbstractId abstractId;        
        BuildObject outputObject;
        BuildObject asmFile;

        public MasmVerb(IAsmProducer asmVerb)
        {            
            this.asmVerb = asmVerb;
            this.asmFile = asmVerb.getAsmFile();

            abstractId = new AbstractId(this.GetType().Name, version, asmFile.ToString());
            outputObject = asmFile.makeOutputObject(OBJ_EXTN);
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        BuildObject getMasmExe()
        {
            return new SourcePath("tools/Assembler/ml.exe", SourcePath.SourceType.sourceTypeTools);
        }

        public BuildObject getObj() { return outputObject; } 
        public BuildObject getLis() { return asmFile.makeOutputObject(".lis"); }
        //-public BuildObject getMap() { return asmFile.makeOutputObject(".map"); }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return new List<BuildObject>() { getMasmExe(), asmVerb.getAsmFile() };
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { asmVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() {
				getObj(),
				getLis()
				
			};
        }

        public override IVerbWorker getWorker()
        {
            List<string> args = new List<string>() { "/Cp", "/c", "/Zd", "/Zf", "/Zi" };
            args.Add("/Fo" + getObj().getRelativePath());
            args.Add("/Fl" + getLis().getRelativePath());
            //-args.Add("/Fm" + getMap().getRelativePath());
            //- TODO: "/I$SPEC_INCLUDE_DIR" 
            args.Add(asmFile.getRelativePath());
    
            return new ProcessInvokeAsyncWorker(this,
                getMasmExe().getRelativePath(), args.ToArray(), ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE, getDiagnosticsBase());            
        }

        public Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            //- No cleanup to do here but pass back the disposition.
            return worker.pinv.disposition;
        }
    }
}

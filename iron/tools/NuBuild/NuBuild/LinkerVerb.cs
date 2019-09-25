using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class LinkerVerb : Verb, IProcessInvokeAsyncVerb
    {        
        public const string UNTRUSTED_EXE_EXTN = ".uexe";
        const int version = 4;

        bool isLoader;
        MasmVerb masmVerb;
        AbstractId abstractId;
        protected BuildObject outputObject;
        protected BuildObject objFile;

        protected long maxExeSize;
        protected string entryPoint;
        protected int baseAddr;

        public LinkerVerb(MasmVerb masmVerb, bool isLoader)
        {            
            this.masmVerb = masmVerb;
            this.isLoader = isLoader;
            this.objFile = masmVerb.getObj();

            abstractId = new AbstractId(this.GetType().Name, version + getVersion(), objFile.ToString(), concrete:isLoader ? "Loader" : "NonLoader");
            outputObject = objFile.makeOutputObject(outputExtension());

            //- Default settings for the apps
            maxExeSize = 1 * 1024 * 1024; //- 1 MB
            entryPoint = "?AppEntryPoint";
            baseAddr = 0x340000;

            if (isLoader)
            {
                //- Override the settings above with loader-specific values
                maxExeSize = 58 * 1024;  //- 58 KB
                entryPoint = "?LoaderEntryPoint";
                baseAddr = 0x300000;
            }

        }

        protected virtual int getVersion() { return 0; }

        protected virtual string outputExtension()
        {
            return UNTRUSTED_EXE_EXTN;
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        protected virtual BuildObject getLinkerExe()
        {
            return new SourcePath("tools/Assembler/link-base.exe", SourcePath.SourceType.sourceTypeTools);
        }

        public BuildObject getUntrustedExe() { return outputObject; }

        protected virtual IEnumerable<BuildObject> getExtraDependencies() { return new List<BuildObject>(); }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            List<BuildObject> basic = new List<BuildObject>() { getLinkerExe(), objFile };
            basic.AddRange(getExtraDependencies());
            return basic;

        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { masmVerb };
        }

        protected virtual IEnumerable<BuildObject> getExtraOutputs() { return new List<BuildObject>(); }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { getUntrustedExe() }.Union(getExtraOutputs());
        }
    
        protected virtual bool runLinker(BuildObject asmFile, string linkerExecutable, string entryPoint, int baseAddr, long maxExeSize = -1)
        {            

            return true;
        }

        public override IVerbWorker getWorker()
        {            
            List<string> args = new List<string>() { "/LARGEADDRESSAWARE", "/driver", "/fixed", "/subsystem:native", "/nodefaultlib" };
            args.Add(objFile.getRelativePath());
            args.Add("/out:" + outputObject.getRelativePath());
            args.Add("/entry:" + entryPoint);
            args.Add("/base:" + baseAddr);

            return new ProcessInvokeAsyncWorker(this,
                getLinkerExe().getRelativePath(), args.ToArray(), ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE, getDiagnosticsBase());
        }

        public virtual Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            if (!(worker.pinv.disposition is Failed))
            {
                //- Check that the executable isn't too large
                long exeSize = new FileInfo(outputObject.getFilesystemPath()).Length;

                if (exeSize > maxExeSize)
                {
                    return new Failed("Executable too big");
                }
            }                     

            return worker.pinv.disposition;
        }
    }
}

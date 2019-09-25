using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class WinLinkerVerb : LinkerVerb
    {        
        public const string WIN_APP_EXE_EXTN = ".winapp";
        const int version = 6;

        public WinLinkerVerb(MasmVerb masmVerb, bool isLoader) : base(masmVerb, isLoader) { } 

        protected override string outputExtension()
        {
            return WIN_APP_EXE_EXTN + UNTRUSTED_EXE_EXTN;
        }

        protected override int getVersion() { return version; }
                
        //- TODO: We should build this!
        protected static SourcePath getStandaloneLib()
        {
           return new SourcePath("tools/standalone/Debug/StandAloneSupport.lib", SourcePath.SourceType.sourceTypeTools);
        }

        protected override IEnumerable<BuildObject> getExtraDependencies() { return new List<BuildObject>() { getStandaloneLib() }; }

        private BuildObject getPdb() { return objFile.makeOutputObject(".pdb"); }
       
        public override IVerbWorker getWorker()
        {
            string linker = @"C:\Program Files (x86)\Microsoft Visual Studio 12.0\VC\bin\link.exe";
            string vc_lib_dir = @"C:\Program Files (x86)\Microsoft Visual Studio 12.0\VC\lib";
            string sdk_dir = @"C:\Program Files (x86)\Windows Kits\8.1\Lib\winv6.3\um\x86";
            string kernel_lib = @"C:\Program Files (x86)\Windows Kits\8.1\Lib\winv6.3\um\x86\kernel32.Lib";
            string standalone_support_lib = getStandaloneLib().getRelativePath();
            SourcePath zero1 = new SourcePath("tools/scripts/zero.obj", SourcePath.SourceType.sourceTypeTools);
            SourcePath zero2 = new SourcePath("tools/scripts/zero2.obj", SourcePath.SourceType.sourceTypeTools);

            //- TODO: Fail more gracefully?  Or better yet, move these into iron/tools
            if (!Directory.Exists(vc_lib_dir)) {
                throw new FileNotFoundException("Missing Visual C++ library directory: " + vc_lib_dir);
            }

            if (!Directory.Exists(sdk_dir) || !File.Exists(kernel_lib)) {
                throw new FileNotFoundException("Missing Windows SDK libraries: " + sdk_dir + ", " + kernel_lib + @". Try installing the Windows SDK from: \\research\Root\Products\Developers\Windows Driver Kit 8.1");
            }

            //- TODO: Unpack/generate these automatically
            if (!File.Exists(zero1.getFilesystemPath()) || !File.Exists(zero2.getFilesystemPath()))
            {
                throw new FileNotFoundException("Missing object files of zeroes: " + zero1 + ", " + zero2 + ".  Try running: tools/scripts/build-standalone-init.sh");
            }

            List<string> args = new List<string>() { "/DEBUG", "/subsystem:console", "/LARGEADDRESSAWARE", "/fixed" };
            args.Add(objFile.getRelativePath());
            args.Add(zero1.getRelativePath());
            args.Add(zero2.getRelativePath());
            args.Add(standalone_support_lib);
            args.Add(@"""" + kernel_lib + @"""");
            args.Add("\"/libpath:" + vc_lib_dir + '"');
            args.Add("\"/libpath:" + sdk_dir + '"');
            args.Add("/out:" + outputObject.getRelativePath());
            args.Add("/entry:" + entryPoint);
            args.Add("/base:" + baseAddr);
            args.Add("/PDB:" + getPdb());

            return new ProcessInvokeAsyncWorker(this,
                linker, args.ToArray(), ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE, getDiagnosticsBase(), allowAbsoluteExe: true, allowAbsoluteArgs: true);         
        }

        protected override IEnumerable<BuildObject> getExtraOutputs()
        {
            List<BuildObject> outputs = new List<BuildObject>();
            outputs.Add(getPdb());
            return outputs;
        }

        public override Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            //- No cleanup to do
            return worker.pinv.disposition;
        }
    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class DafnyCCVerb
        : DafnyTransformBaseVerb
    {
        AbstractId abstractId;
        public enum FramePointerMode { UseFramePointer, NoFramePointer };
        FramePointerMode useFramePointer;
        VSSolutionVerb dafnyCCBuildExecutableVerb = new VSSolutionVerb(new SourcePath("tools/DafnyCC/DafnyCC.sln", SourcePath.SourceType.sourceTypeTools));

        public DafnyCCVerb(SourcePath dfyroot, string appLabel, FramePointerMode useFramePointer)
            : base(dfyroot, appLabel)
        {
            this.useFramePointer = useFramePointer;
            abstractId = new AbstractId(this.GetType().Name, getVersion() + version, dfyroot.ToString(), concrete:useFramePointer.ToString());                            
        }

        protected override int getVersion() { return 17; }

        public override AbstractId getAbstractIdentifier() { return abstractId; }
     
        protected override BuildObject getExecutable()
        {
            return new BuildObject(Path.Combine(dafnyCCBuildExecutableVerb.getOutputPath().getRelativePath(), "dafnycc.exe"));
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return base.getVerbs().Concat(new [] { dafnyCCBuildExecutableVerb } );
        }

        protected override IEnumerable<BuildObject> getExtraDependencies()
        {
            return new BuildObject[] { getDafnyPrelude(), getExecutable() };
        }

        protected override IEnumerable<SourcePath> getRootArgs()
        {
            DependencyDisposition ddisp;
            IEnumerable<SourcePath>  result = getAllDafnyModules(out ddisp);
            Util.Assert(ddisp == DependencyDisposition.Complete);
            return result;
        }

        protected override IEnumerable<string> getExtraSpecialOutputs()
        {
            //- Work around some undesirable behavior presently in DafnyCC:
			//- We can't pass DafnyPrelude on the command line (getRootArgs) to DafnyCC,
            //- yet it emits a dafny_DafnyPrelude file that we want to account for in the output.
            return new string[] { "Checked", "Heap", "Seq", "dafny_DafnyPrelude" };
        }

        protected override void addExtraArgs(List<string> args)
        {
            args.Add("/relational");
            if (useFramePointer == FramePointerMode.UseFramePointer) {
                args.Add("/useFramePointer");
            }
        }

        protected override IEnumerable<SourcePath> getRoots()
        {
            return new SourcePath[] {
                new SourcePath("src/Trusted/DafnySpec/Seq.s.dfy"),
                new SourcePath("src/Checked/Libraries/DafnyCC/Seq.dfy"),
                dfyroot };
        }

        //- This is merely an assert double-check that we didn't let a spec generated
        //- by DafnyCC slip through to be used in the BoogieAsmVerify step.
        internal static void AssertSmellsImplementy(BuildObject obj)
        {
            string fn = obj.getFileNameWithoutExtension();
            Util.Assert(fn.EndsWith("_"+DAFNY_I_SUFFIX)
                || fn.EndsWith("_"+DAFNY_C_SUFFIX)
                || fn.Equals("Checked")
                || fn.Equals("Heap")
                || fn.Equals("Seq"));
        }
    }
}

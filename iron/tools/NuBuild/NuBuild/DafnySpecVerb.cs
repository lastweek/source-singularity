using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class DafnySpecVerb
        : DafnyTransformBaseVerb
    {
        AbstractId abstractId;
        private VSSolutionVerb dafnySpecBuildExecutableVerb = new VSSolutionVerb(new SourcePath("tools/DafnySpec/DafnySpec.sln", SourcePath.SourceType.sourceTypeTools));

        public DafnySpecVerb(SourcePath dfyroot, string appLabel)
            : base(dfyroot, appLabel)
        {
            abstractId = new AbstractId(this.GetType().Name, getVersion() + version, dfyroot.ToString());
        }

        protected override int getVersion() { return 15; }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        protected override BuildObject getExecutable()
        {
            return new BuildObject(Path.Combine(dafnySpecBuildExecutableVerb.getOutputPath().getRelativePath(), "dafnyspec.exe"));
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return base.getVerbs().Concat(new [] { dafnySpecBuildExecutableVerb } );
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            return base.getDependencies(out ddisp).Concat(new [] { getExecutable() });
        }

        protected override IEnumerable<SourcePath> getRoots()
        {
            //- TODO why doesn't DafnyCC require DafnyPreludePath?
            return new SourcePath[] { getDafnyPrelude(), getSeqSpec(), dfyroot };
        }

        private SourcePath getSeqSpec() { return new SourcePath("src/Trusted/DafnySpec/Seq.s.dfy"); }


        protected override bool transformFilterAccepts(BuildObject dfysource)
        {
            string fn = dfysource.getFileNameWithoutExtension();
            if (fn.EndsWith("."+DAFNY_S_SUFFIX))
            {
                return true;
            }
            else
            {
                Util.Assert(fn.EndsWith("."+DAFNY_I_SUFFIX) || fn.EndsWith("."+DAFNY_C_SUFFIX) || dfysource.Equals(getDafnyPrelude()));
                return false;
            }
        }

        protected override IEnumerable<SourcePath> getRootArgs()
        {
            OrderPreservingSet<SourcePath> specFiles = new OrderPreservingSet<SourcePath>();
            specFiles.Add(getDafnyPrelude());
            specFiles.Add(getSeqSpec());
            DependencyDisposition ddisp;
            foreach (SourcePath src in getAllDafnyModules(out ddisp))
            {
                if (transformFilterAccepts(src))
                {
                    specFiles.Add(src);
                }
            }

            return specFiles;
        }
    }
}

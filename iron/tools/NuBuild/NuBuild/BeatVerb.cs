using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class BeatVerb
        : Verb, IProcessInvokeAsyncVerb
    {
        public static bool isBeat(BuildObject obj)
        {
            return obj.getExtension().Equals(BeatExtensions.BEATIFC_EXTN)
                || obj.getExtension().Equals(BeatExtensions.BEATIMP_EXTN);
        }

        const int version = 34;

        IContextGeneratingVerb contextVerb;
        BuildObject beatobj;
        string appLabel;
        AbstractId abstractId;

        static NmakeVerb _beatBuildExecutableVerb; 
        private NmakeVerb getBeatBuildExecutableVerb()
        {
            if (_beatBuildExecutableVerb == null)
            {
                _beatBuildExecutableVerb = new NmakeVerb(new SourcePath("tools/Beat/makefile", SourcePath.SourceType.sourceTypeTools));
            }
            return _beatBuildExecutableVerb;
        }

        public BeatVerb(IContextGeneratingVerb contextVerb, BuildObject beatobj, string appLabel)
        {
            this.contextVerb = contextVerb;
            this.beatobj = beatobj;
            this.appLabel = appLabel;
            this.abstractId = new AbstractId(this.GetType().Name, version, beatobj.ToString(), contextVerb.getPoundDefines(), concrete:appLabel);
        }

        private string getModuleNameForObj(BuildObject obj)
        {
            return obj.getFileNameWithoutExtension();
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            OrderPreservingSet<BuildObject> deps = BeatExtensions.getBeatFlavoredShallowDependencies(
                contextVerb, beatobj, out ddisp, BeatIncludes.ImportFilter.ForBeatOrBasm);
            deps.Add(getBeatExecutable());
            return deps;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { contextVerb, getBeatBuildExecutableVerb() };
        }

        BuildObject outputFile()
        {
            string outputAppLabel = (appLabel==null ? "" : appLabel) + contextVerb.getPoundDefines().ToString();
            string extn = beatobj.getExtension().Equals(BeatExtensions.BEATIFC_EXTN) ? BoogieAsmVerifyVerb.BASMIFC_EXTN : BoogieAsmVerifyVerb.BASMIMP_EXTN;
            return beatobj.makeLabeledOutputObject(outputAppLabel, extn);
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { outputFile() };
        }

        public override AbstractId getAbstractIdentifier()
        {
            return abstractId;
        }

        public BuildObject getBeatExecutable()
        {
            return new BuildObject(Path.Combine(getBeatBuildExecutableVerb().getOutputPath().getRelativePath(), "beat.exe"));
        }

        public override IVerbWorker getWorker()
        {
            //-        "beat $BUILD_DEFS -out $out.tmp -in $in $incls"
            List<string> args = new List<string>();
            args.Add("-in");
            args.Add(beatobj.getRelativePath());

            IEnumerable<BuildObject> beatImports =
                BeatExtensions.getBeatFlavoredShallowIncludes(contextVerb, beatobj, BeatIncludes.ImportFilter.ForBeatOrBasm);
            foreach (BuildObject ifcObj in beatImports.Where(obj => !obj.Equals(beatobj)))
            {
                Util.Assert(!ifcObj.getRelativePath().Contains(".imp"));   //- Erk, don't feed imp files as includes!
                args.Add("-i");
                args.Add(ifcObj.getRelativePath());
            }
            args.AddRange(contextVerb.getPoundDefines().ToDefArgs());

            string dbgText = String.Format("rem verb {0}{1}",
                this, System.Environment.NewLine);

            return new ProcessInvokeAsyncWorker(this,
                    getBeatExecutable().getRelativePath(),
                    args.ToArray(),
                    ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE,
                    finalStdoutPath:outputFile().getFilesystemPath(),
                    failureBase:getDiagnosticsBase(),
                    dbgText:dbgText);
        }

        public Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            if (worker.pinv.disposition is Fresh)
            {
                BeatExtensions.propagatePrivateImports(contextVerb, beatobj, outputFile());

                //- And then propagate the NuBuild annotations, too.
                AnnotationScanner.transferAnnotations(
                    beatobj, outputFile(), BoogieAsmDepBase.CommentSymbol);
            }

            return worker.pinv.disposition;
        }
    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class BoogieAsmVerifyVerb
            : BoogieAsmWorkerBase
    {
        public const string MUTUAL_SUMMARY_EXTN = ".ms";
        public const string SYMDIFF_EXTN = ".symdiff";
        public const string SYMDIFF_DIR_EXTN = ".dir";

        bool buildSymDiffMutualSummary;
        bool enableSymdiff = false;

        protected override int getVersion() { return 19; }
        protected override string getAction() { return "-verify"; }
        protected override bool outFlagWorks() { return true; }
        protected override bool includeAllImps() { return false; }
        protected override string getExtraAbstractID() { return buildSymDiffMutualSummary ? ", relational" : ", functional"; }

        public override BuildObject outputFile()
        {
            if (buildSymDiffMutualSummary)
            {
                //- SymDiff files need to go into their own directory
                BuildObject normalName = BeatExtensions.makeOutputObject(basmInput, SYMDIFF_EXTN);
                
                //- The following produces file names that are too long in the failures directory.
                //- The OS then truncates them, causing filename collisions.
                //-BuildObject dirExtendedName = new BuildObject(Path.Combine(normalName.getDirPath(), Util.mungeClean(getAbstractIdentifier()), normalName.getFileName()));
                //- Try naming the directory after the file instead
                BuildObject dirExtendedName = new BuildObject(Path.Combine(normalName.getDirPath(), normalName.getFileName() + SYMDIFF_DIR_EXTN, normalName.getFileName()));

                return dirExtendedName;
            }
            else
            {
                return BeatExtensions.makeOutputObject(basmInput, BoogieVerb.BPL_EXTN);
            }
        }

        public BoogieAsmVerifyVerb(IContextGeneratingVerb context, BuildObject input, bool buildSymDiffMutualSummary)
            : base(context, input)
        {
            this.buildSymDiffMutualSummary = buildSymDiffMutualSummary;
            this.enableSymdiff = BoogieAsmVerifyVerb.needs_symdiff(basmInput);
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            
            return getVerifyishVerbs();
        }

        const string AddBoogieAxiomAnnotation = "AddBoogieAxiom";
        const string BasmEnableSymdiffAnnotation = "BasmEnableSymdiff";

        public static bool needs_symdiff(BuildObject basm)
        {
            AnnotationScanner annotations = new AnnotationScanner(basm);
            bool symdiff = false;
            foreach (string[] ann in annotations.getAnnotations(BasmEnableSymdiffAnnotation))
            {
                if (ann.Length != 2
                    || !ann[1].Equals("true"))
                {
                    throw new SourceConfigurationError("Expected " + BasmEnableSymdiffAnnotation + " to have argument 'true'.");
                }
                symdiff = true;
            }

            return symdiff;
        }


        IEnumerable<SourcePath> getTrustedBoogieAxioms()
        {
            OrderPreservingSet<SourcePath> result = new OrderPreservingSet<SourcePath>();
            AnnotationScanner anns = new AnnotationScanner(basmInput);
            foreach (string[] annotation in anns.getAnnotations(AddBoogieAxiomAnnotation))
            {
                string module = annotation[1];
                SourcePath trustedPath = new SourcePath(Path.Combine(
                    BuildEngine.theEngine.getSrcRoot(),
                    BuildEngine.VerveTrustedSpecDir,
                    module+BoogieVerb.BPL_EXTN));
                result.Add(trustedPath);
            }
            return result;
        }

        protected override IEnumerable<BuildObject> getExtraDeps(out DependencyDisposition ddisp)
        {
            try
            {
                ddisp = DependencyDisposition.Complete;
                return getTrustedBoogieAxioms();
            }
            catch (ObjNotReadyException)
            {
                //- All the basms aren't here yet, so we can't scan them. Don't sweat it;
                //- those deps are already being called for.
                ddisp = DependencyDisposition.Incomplete;
                return new BuildObject[] { };
            }
            catch (ObjFailedException)
            {
                ddisp = DependencyDisposition.Failed;
                return new BuildObject[] { };
            }
        }

        public BuildObject getMutualSummary()
        {
            //- SymDiff files need to go into their own directory
            BuildObject normalName = BeatExtensions.makeOutputObject(basmInput, MUTUAL_SUMMARY_EXTN);
            BuildObject dirExtendedName = new BuildObject(Path.Combine(normalName.getDirPath(), Util.mungeClean(getAbstractIdentifier().ToString()), normalName.getFileName()));

            return dirExtendedName;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            List<BuildObject> outputs = new List<BuildObject> { outputFile() };
            if (buildSymDiffMutualSummary)
            {
                outputs.Add(getMutualSummary());
            }
            return outputs;
        }

        protected override void extendArgs(List<string> args)
        {            
            
            if (!buildSymDiffMutualSummary && enableSymdiff)
            {
                args.Add("-symdiffok");
            }
            else if (buildSymDiffMutualSummary)
            {
                args.Add("-symdiffms");
                args.Add(getMutualSummary().getRelativePath());
            }

            //-foreach (SourcePath includedAxiom in getTrustedBoogieAxioms(acc.basmModules))
            foreach (SourcePath includedAxiom in getTrustedBoogieAxioms())
            {
                if (!includedAxiom.isTrusted)
                {
                    throw new SourceConfigurationError(AddBoogieAxiomAnnotation + " annotation points at untrusted file " + includedAxiom.ToString());
                }
                //- SECURITY POLICY: you can only include trusted things labeled "_axioms.bpl".
                if (!includedAxiom.getExtension().Equals(BoogieVerb.BPL_EXTN)
                    || !includedAxiom.getFileNameWithoutExtension().EndsWith("_axioms"))
                {
                    throw new SourceConfigurationError(AddBoogieAxiomAnnotation + " annotation points at file that isn't a Boogie axioms file: " + includedAxiom.ToString());
                }

                args.Add("/trustedBoogie:" + includedAxiom.getRelativePath());
            }
        }

        protected override void postprocess()
        {
            AnnotationScanner.transferAnnotations(basmInput, outputFile(), BoogieVerb.CommentSymbol);
        }
    }
}

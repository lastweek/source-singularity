using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class BoogieVerb
        : VerificationResultVerb, IProcessInvokeAsyncVerb
    {
        public const string BPL_EXTN = ".bpl";
        public const string CommentSymbol = "//-";

        const int version = 15;
        const string AddBoogieFlagAnnotation = "AddBoogieFlag";

        BuildObject bplInput;
        AbstractId abstractId;
        IEnumerable<IVerb> upstreamVerbs;
        int timeLimit = 300;

        public BoogieVerb(IContextGeneratingVerb context, BuildObject bplInput, VerificationRequest.SymDiffMode symdiff)
        {
            if (bplInput.getExtension().Equals(BPL_EXTN))
            {
                this.bplInput = bplInput;
                upstreamVerbs = new List<IVerb>();
                //- TODO this will probably break, since we don't know where this bplInput came from. Maybe that's okay, since the verb had to already exist to reach this point.
            }
            else if (symdiff == VerificationRequest.SymDiffMode.NoSymDiff)
            {
                IVerb boogieAsmVerb = new BoogieAsmVerifyVerb(context, bplInput, false);
                this.bplInput = boogieAsmVerb.getOutputs().First();
                upstreamVerbs = new IVerb[] { boogieAsmVerb };
            }
            else
            {
                IVerb workerVerb;
                SymDiffEngine.BuildPipeline(context, bplInput, out this.bplInput, out workerVerb);
                upstreamVerbs = new IVerb[] { workerVerb };
            }

            this.abstractId = new AbstractId(this.GetType().Name, version, bplInput.ToString(),
                concrete: symdiff.ToString());
        }

        protected override BuildObject getSource() { return bplInput; }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            //- If you've got the boogieinput file, you're done.
            ddisp = DependencyDisposition.Complete;
            return new BuildObject[] { bplInput };
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return upstreamVerbs;
        }

        public override BuildObject getOutputFile()
        {
            return BeatExtensions.makeOutputObject(bplInput, BPL_EXTN + VerificationResultVerb.VERIFICATION_RESULT_EXTN);
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { getOutputFile() };
        }

        public override AbstractId getAbstractIdentifier()
        {
            return abstractId;
        }

        //- SECURITY POLICY: we only allow checked files to specify the flags below.
        //- Otherwise, one might thing it reasonable to specify "/noVerify:1" or something.
        static readonly string[] validFlagsAnyValue = { "/restartProver", "/timeLimit", "/trace" };
        static readonly string[] validFlagsSpecificValues = { "/proverOpt:OPTIMIZE_FOR_BV=true", "/z3opt:NL_ARITH=false" };

        private IEnumerable<string> getFlags()
        {
            List<string> flags = new List<string>();
            foreach (string[] ann in new AnnotationScanner(bplInput).getAnnotations(AddBoogieFlagAnnotation))
            {
                if (ann.Count()!=2) {
                    throw new SourceConfigurationError(bplInput + " has malformed annotation: " + String.Join(" ", ann));
                }
                string flag = ann[1];
                string[] flagParts = flag.Split(new char[] { ':' }, 2);
                if (validFlagsAnyValue.Contains(flagParts[0]))
                {
                    flags.Add(flag);
                }
                else if (validFlagsSpecificValues.Contains(flag))
                {
                    flags.Add(flag);
                }
                else
                {
                    throw new SourceConfigurationError(bplInput + " contains disallowed flag " + flag);
                }
                if (flagParts[0].Equals("/timeLimit"))
                {
                    Util.Assert(flagParts.Count() == 2);
                    timeLimit = Int32.Parse(flagParts[1]);
                }
            }
            return flags;
        }

        public override IVerbWorker getWorker()
        {
            if (false)
            {
#pragma warning disable 162
                File.WriteAllText(getOutputFile().getFilesystemPath(), "Verification disabled temporarily for debugging");
                return new VerbSyncWorker(new Fresh());
#pragma warning restore 162
            }

            SourcePath boogieExecutable = new SourcePath("tools/Dafny/Boogie.exe", SourcePath.SourceType.sourceTypeTools);

            List<string> args = new List<string>();
            args.Add("/noinfer");
            args.Add("/typeEncoding:m");
            args.Add("/z3opt:ARITH_RANDOM_SEED=1");
            args.Add("/timeLimit:"+timeLimit);
            args.AddRange(getFlags());
            args.Add(bplInput.getRelativePath());

            return new ProcessInvokeAsyncWorker(this,
                    boogieExecutable.getRelativePath(),
                    args.ToArray(),
                    ProcessInvoker.RcHandling.NONZERO_RC_IS_OKAY,
                    getDiagnosticsBase());
        }

        public Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            VerificationResult vr = new VerificationResult(bplInput.getRelativePath(), worker.pinv, new VerificationResultBoogieParser());
            vr.addBasicPresentation();
            vr.toXmlFile(getOutputFile().getFilesystemPath());
            setWasVerificationTimeout(vr.wasOnlyTimeouts());
            return worker.pinv.disposition;
        }
    }
}}
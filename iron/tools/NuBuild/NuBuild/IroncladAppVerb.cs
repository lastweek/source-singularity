using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class IroncladAppVerb
        : Verb, IObligationsProducer
    {
        const int version = 5;
        public const string TRUSTED_EXE_EXTN = ".exe";
        public const string UNVERIFIED_SENTINEL_EXTENSION = ".usentinel";
        public enum TARGET { BARE_METAL, WINDOWS };
        //-public enum VerifyMode { Verify, NoVerify };
        //-public enum SymDiffMode { UseSymDiff, NoSymDiff };


        SourcePath dfyroot;
        AbstractId abstractId;
        DafnySpecVerb dafnyspecVerb;
        DafnyCCVerb dafnyccVerb;
        EntryStitcherVerb stitcherVerb;
        VerificationResultSummaryVerb verifyResultsVerb;
        LinkerVerb linkerVerb;
        PoundDefines poundDefines;
        VerificationRequest verificationRequest;
        string appLabel;

        BuildObject srcObject;
        BuildObject exeObject;
        BuildObject outputObject;

        public IroncladAppVerb(SourcePath dfyroot, TARGET target, DafnyCCVerb.FramePointerMode framePointerMode, VerificationRequest verificationRequest)
        {
            this.dfyroot = dfyroot;

            //- TODO this is the only #define we support just yet, so I'm stuffing it in here.
            //- We'll need to plumb more carefully when we want to add x64.
            if (dfyroot.getDirPath().Split(Path.DirectorySeparatorChar).Last().Equals("AppLoader"))
            {
                this.poundDefines = new PoundDefines(new string[] { "AppLoader" });
            }
            else
            {
                this.poundDefines = PoundDefines.empty();
            }

            this.verificationRequest = verificationRequest;
            this.abstractId = new AbstractId(this.GetType().Name, version, dfyroot.ToString(),
                poundDefines,
                concrete:String.Format("{0},{1},{2}",
                    target, 
                    framePointerMode.ToString(),
                    verificationRequest.ToString()
                ));
            appLabel = dfyroot.getDirPath().Split(Path.DirectorySeparatorChar).Last();
            dafnyspecVerb = new DafnySpecVerb(dfyroot, appLabel);
            dafnyccVerb = new DafnyCCVerb(dfyroot, appLabel, framePointerMode);

            bool isLoader = dfyroot.getRelativePath().Equals(BootableAppVerb.LOADER_DFY);

            //- NB we keep dafnyccVerb as the lowest-priority context, so that our hand-written
            //- beat impls will override its output.
            IContextGeneratingVerb contextWithDafny = new ConcatContextVerb(
                BuildEngine.theEngine.getVerveContextVerb(poundDefines),
                new VerbOutputsContextVerb(dafnyspecVerb, false),
                new VerbOutputsContextVerb(dafnyccVerb, true),
                poundDefines);
            stitcherVerb = new EntryStitcherVerb(contextWithDafny, appLabel);
            IContextGeneratingVerb contextWithDafnyAndEntry = new ConcatContextVerb(
                new VerbOutputsContextVerb(stitcherVerb, false),
                contextWithDafny,
                poundDefines);

            BuildObject entryImpObj = stitcherVerb.getEntryImpOutput();
            BoogieAsmLinkVerb entryVerb = new BoogieAsmLinkVerb(contextWithDafnyAndEntry, entryImpObj);
            if (target == TARGET.BARE_METAL) {
                MasmVerb masmVerb = new MasmVerb(entryVerb);            
                linkerVerb = new LinkerVerb(masmVerb, isLoader);
            } else if (target == TARGET.WINDOWS) {     //- Rewrite the asm that comes out of entryVerb before linking it
                AsmRewriterVerb rewriter = new AsmRewriterVerb(entryVerb);
                MasmVerb masmVerb = new MasmVerb(rewriter);
                linkerVerb = new WinLinkerVerb(masmVerb, isLoader);
            }

            BoogieAsmVerificationObligationListVerb bavolVerb =
                new BoogieAsmVerificationObligationListVerb(contextWithDafnyAndEntry, entryImpObj, verificationRequest);

            verifyResultsVerb = new VerificationResultSummaryVerb(bavolVerb);

            srcObject = linkerVerb.getUntrustedExe();
            if (verificationRequest.isComplete())
            {
                exeObject = dfyroot.makeOutputObject(TRUSTED_EXE_EXTN);
                outputObject = exeObject;
            }
            else
            {
                exeObject = srcObject;
                outputObject = dfyroot.makeVirtualObject(UNVERIFIED_SENTINEL_EXTENSION);
            }
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            List<BuildObject> result = new List<BuildObject>();
            result.Add(srcObject);

            result.Add(verifyResultsVerb.getOutputFile());

            ddisp = DependencyDisposition.Complete;
                    
            return result;
        }   

        public override IVerbWorker getWorker() {
            if (verificationRequest.isComplete())
            {
                //- If the verification succeeded, then we convert the untrusted exe into a trusted exe (via a copy)
                VerificationResult vr = VerificationResult.fromXmlFile(verifyResultsVerb.getOutputFile().getFilesystemPath());

                if (!vr.pass)
                {
                    return new VerbSyncWorker(new Failed());
                }

                File.Copy(srcObject.getFilesystemPath(), outputObject.getFilesystemPath(), true);   //- True => Overwrite
            }
            else
            {
                UnverifiedSentinelVirtualContents contents = new UnverifiedSentinelVirtualContents();
                BuildEngine.theEngine.getNuObjContents().storeVirtual(outputObject, new Fresh(), contents);
            }
            return new VerbSyncWorker(new Fresh());
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            List<IVerb> result = new List<IVerb>();
            result.Add(dafnyccVerb);            
            result.Add(stitcherVerb);
            result.Add(linkerVerb);
            result.Add(verifyResultsVerb);
            result.AddRange(verifyResultsVerb.getVerbs());   //- Sleazy.
            return result;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { outputObject };
        }

        public BuildObject getObligationSet() 
        {
            return verifyResultsVerb.getObligationSet();
        }

        public override AbstractId getAbstractIdentifier()
        {
            return abstractId;
        }

        public BuildObject getExe() { return exeObject; }

        public override Presentation getPresentation()
        {
            return verifyResultsVerb.getPresentation();
        }

        public string getAppLabel() { return appLabel; }
    }
}

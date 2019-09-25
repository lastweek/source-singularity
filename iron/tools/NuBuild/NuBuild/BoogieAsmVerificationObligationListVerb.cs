using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    //- NB we generate the obligation list in a seperate verb from the actual BoogieAsm -link step
    //- because the latter is quite slow, and the former frees up a bunch of downstream
    //- parallelism.
    class BoogieAsmVerificationObligationListVerb
        : BoogieAsmDepBase, IObligationsProducer
    {
        BuildObject obligations;
        VerificationRequest verificationRequest;

        protected override int getVersion() { return 5; }
        protected override bool includeAllImps() { return true; }

        protected override string getExtraAbstractID() { return verificationRequest.ToString(); }

        public override BuildObject outputFile()
        {
            return obligations;
        }

        public BoogieAsmVerificationObligationListVerb(IContextGeneratingVerb context, BuildObject input, VerificationRequest verificationRequest)
            : base(context, input)
        {
            this.verificationRequest = verificationRequest;
            obligations = input.makeOutputObject(BASM_EXTN + VerificationObligationList.VOL_EXTN);
        }

        public BuildObject getObligationSet() { return obligations; }

        public override IEnumerable<IVerb> getVerbs()
        {
            IEnumerable<IVerb> result = getVerifyishVerbs();
            IEnumerable<IVerb> boogieVerbs = new List<BoogieVerb>(); 
            try {
                boogieVerbs = getBoogieVerbs(verificationRequest);
                //-Logger.Out.WriteLine("Successfully retrieved the Boogie verbs.");
            } catch (ObjNotReadyException) {
                //-Logger.Out.WriteLine("Caught an exception: " + e);
            }
            return result.Concat(boogieVerbs);
        }

        public IEnumerable<IVerb> getObligationSatisfyingVerbs()
        {
            return getBoogieVerbs(verificationRequest);
        }

        public override IVerbWorker getWorker()
        {
            IEnumerable<BuildObject> verificationResults = getBoogieVerbs(verificationRequest)
                .Select(boogie_verb => boogie_verb.getOutputFile());
            VerificationObligationList vol = new VerificationObligationList(verificationResults);
            vol.store(this.obligations);
            return new VerbSyncWorker(new Fresh());
        }

    }
}

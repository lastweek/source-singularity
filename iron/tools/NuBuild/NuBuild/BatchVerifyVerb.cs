using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class BatchVerifyVerb
        : Verb, IObligationsProducer
    {
        const string BATCH_EXTN = ".batch";
        const int version = 1;
        public enum BatchMode { DAFNY, APP };

        BuildObject outputObject;
        HashSet<IObligationsProducer> producers;
        AbstractId abstractId;
        BatchMode mode;
        List<BuildObject> deps;

        public BatchVerifyVerb(SourcePath batch_file, BatchMode mode, VerificationRequest verificationRequest, DafnyCCVerb.FramePointerMode useFramePointer)
        {
            this.mode = mode;

            this.producers = new HashSet<IObligationsProducer>();
            foreach (string line in File.ReadAllLines(batch_file.getFilesystemPath())) {
                if (line[0] == '#')
                {
                    continue;
                }
                SourcePath src = new SourcePath(line);
                switch (mode) {
                    case BatchMode.DAFNY:
                        if (verificationRequest.verifyMode != VerificationRequest.VerifyMode.Verify)
                        {
                            throw new UserError("BatchVerify DAFNY only supports full verification (but maybe we should add selective?)");
                        }
                        this.producers.Add(new DafnyVerifyTreeVerb(src));
                        break;
                    case BatchMode.APP:
                        this.producers.Add(new IroncladAppVerb(src, IroncladAppVerb.TARGET.BARE_METAL, useFramePointer, verificationRequest));
                        break;
                    default:
                        throw new Exception("Unknown batch file type");
                }
            }

            string parameters = mode.ToString() + "," + verificationRequest.ToString();
            outputObject = batch_file.makeLabeledOutputObject(parameters, BATCH_EXTN + VerificationObligationList.VOL_EXTN);
            abstractId = new AbstractId(this.GetType().Name, version, batch_file.ToString(), concrete:parameters);
        }

        public BatchVerifyVerb(BuildObject batch_label, HashSet<IObligationsProducer> producers, BatchMode mode) {            
            this.mode = mode;
            this.producers = producers;

            outputObject = batch_label.makeOutputObject(BATCH_EXTN + VerificationObligationList.VOL_EXTN);
            abstractId = new AbstractId(this.GetType().Name, version, batch_label.ToString(), concrete:mode.ToString());            
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        public BuildObject getObligationSet() { return outputObject; }


        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp) {
            if (this.deps == null) {
                this.deps = new List<BuildObject>();
                foreach (IObligationsProducer producer in producers) {
                    this.deps.Add(producer.getObligationSet());
                }                
            }

            ddisp = DependencyDisposition.Complete;
            return this.deps;
        }

        public override IEnumerable<IVerb> getVerbs() 
        {
            //- pass this request upstream to expose upstream verbs.
            HashSet<IVerb> upstreamVerbs = new HashSet<IVerb>();
            foreach (IVerb producer in producers)
            {
                upstreamVerbs.UnionWith(producer.getVerbs());
                upstreamVerbs.Add(producer);
            }
            return upstreamVerbs;
        }


        public override IEnumerable<BuildObject> getOutputs() {
            return new HashSet<BuildObject>() { outputObject };
        }

        public override IVerbWorker getWorker() 
        {
            //- Coallesce the VerificationObligationLists from each producer into a single result set
            IEnumerable<BuildObject> master = new HashSet<BuildObject>();
            foreach (IObligationsProducer producer in producers) {
                VerificationObligationList vol = VerificationObligationList.fetch(producer.getObligationSet());
                master = master.Union(vol.getVerificationObligations());
            }

            VerificationObligationList myVOL = new VerificationObligationList(master);
            myVOL.store(this.outputObject);
            return new VerbSyncWorker(new Fresh());
        }
    }
}}
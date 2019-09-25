using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class VerificationResultSummaryVerb
        : VerificationResultVerb //-, IObligationsProducer
    {
        const string SUMMARY_EXTN = ".summary";
        const int version = 2;

        BuildObject outputObject;
        IObligationsProducer producer;
        IEnumerable<BuildObject> verification_results;
        AbstractId abstractId;

        public VerificationResultSummaryVerb(IObligationsProducer producer) 
        {
            this.producer = producer;
            BuildObject id = producer.getObligationSet(); //-producer.getIdentifier();
            outputObject = id.makeOutputObject(id.getExtension() + SUMMARY_EXTN);
            abstractId = new AbstractId(this.GetType().Name, version, id.ToString());
            verification_results = null;
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            BuildObject obligations = producer.getObligationSet();
            HashSet<BuildObject> deps = new HashSet<BuildObject>();
            deps.Add(obligations);

            try
            {
                VerificationObligationList vol = VerificationObligationList.fetch(obligations);
                this.verification_results = vol.getVerificationObligations();
                deps.UnionWith(this.verification_results);
                ddisp = DependencyDisposition.Complete;
            }
            catch (ObjNotReadyException)
            {
                ddisp = DependencyDisposition.Incomplete;
            }
            catch (ObjFailedException)
            {
                ddisp = DependencyDisposition.Failed;
            }

            return deps;
        }

        public override IEnumerable<IVerb> getVerbs() 
        {
            IEnumerable<IVerb> verbs = new IVerb[] { producer };

            verbs = verbs.Union(producer.getVerbs());
            return verbs;
            //-            VerificationResultSummaryVerb depends on objects mentioned by producer,
            //-but the necessary verbs haven't been mentioned. Is it sufficient for
            //-the upstream guy (BoogieAsmVerificationObligationList) to ... hopefully ...
            //-mention them? (Hopefully because he might only be incompletely queried,
            //-since he's not actually dependent on the verbs he's advertising.)
            //-Maybe we should provide a way for his complete() method to push the
            //-verbs into the cache.
        }

        public override IEnumerable<BuildObject> getOutputs() {
            return new HashSet<BuildObject>() { outputObject };
        }

        protected override BuildObject getSource() { return producer.getObligationSet(); }
        public override BuildObject getOutputFile() { return outputObject; }

        public BuildObject getObligationSet() { return producer.getObligationSet(); }

        int ByCpuTimeDecreasing(VerificationResult va, VerificationResult vb)
        {
            return -(va.cpuTime.CompareTo(vb.cpuTime));
        }

        string colorByFailureCount(int count)
        {
            return count == 0 ? Presentation.GREEN : Presentation.RED;
        }

        public override IVerbWorker getWorker()
        {
            //- read and aggregate all the input results.
            int parseFailures = 0;
            int verificationFailures = 0;
            int timeouts = 0;
            int filesWithParseFailures = 0;
            int filesWithVerificationFailures = 0;
            int filesWithTimeouts = 0;
            int passCount = 0;
            int failCount = 0;
            double cpuTime = 0;
            List<VerificationMessage> failMessages = new List<VerificationMessage>();
            List<VerificationResult> results = new List<VerificationResult>();

            IEnumerable<BuildObject> verificationResults = verification_results;
            foreach (BuildObject verificationResult in verificationResults)
            {
                VerificationResult vr = VerificationResult.fromXmlFile(verificationResult.getFilesystemPath());
                results.Add(vr);
                if (vr == null)
                {
                    return new VerbSyncWorker(
                        new Failed("Build system broke: missing VerificationResult for " + verificationResult));
                }
                if (vr.pass)
                {
                    passCount += 1;
                }
                else
                {
                    failCount += 1;
                    failMessages.AddRange(vr.getMessages());
                }
                parseFailures += vr.parseFailures;
                verificationFailures += vr.verificationFailures;
                timeouts += vr.timeouts;
                filesWithParseFailures += vr.parseFailures > 0 ? 1 : 0;
                filesWithVerificationFailures += vr.verificationFailures > 0 ? 1 : 0;
                filesWithTimeouts += vr.timeouts > 0 ? 1 : 0;
                //-Logger.WriteLine("Synthesizing cpuTime from " + verificationResult);
                cpuTime += vr.cpuTime;
            }
            bool allPass = failCount == 0;

            PresentationBuilder pr = new PresentationBuilder();

            int any_failures = parseFailures + verificationFailures + timeouts;
            string overall_status = any_failures > 0 ? "Fail" : "Success";

            pr.pre("Git info goes here.\n");
            pr.spacer();
            pr.startHeader();
            pr.color(colorByFailureCount(any_failures), "Overall status: " + overall_status);
            pr.endHeader();
            pr.line("Count of files with failures: " + failCount);
            pr.startBullet();
            pr.color(colorByFailureCount(filesWithParseFailures), "Files with parse failures: " + filesWithParseFailures.ToString());
            pr.endBullet();
            pr.startBullet();
            pr.color(colorByFailureCount(filesWithVerificationFailures), "Files with verification failures: " + filesWithVerificationFailures.ToString());
            pr.endBullet();
            pr.startBullet();
            pr.color(colorByFailureCount(filesWithTimeouts), "Files with timeouts: " + filesWithTimeouts.ToString());
            pr.endBullet();

            pr.spacer();
            pr.header(String.Format("Total processing time: {0:0.0}s {1}", cpuTime, new TimeSpan((long)(cpuTime * 10000000L))));
            int top_n = 10;
            pr.header(String.Format("Slowest {0} verifications:", top_n));

            results.Sort(ByCpuTimeDecreasing);
            foreach (VerificationResult slowResult in results.Take(top_n))
            {
                pr.startBullet();
                pr.color(colorByFailureCount(slowResult.pass ? 0 : 1),
                    String.Format("{0,6:##0.0}s {1}", slowResult.cpuTime, slowResult.sourceLabel));
                pr.endBullet();
            }

            foreach (VerificationMessage message in failMessages)
            {
                pr.spacer();
                pr.header("Failure with " + message.sourceLabel);
                pr.pre(message.message);
            }
            Presentation pres = pr.fix();

            VerificationResult outvr = new VerificationResult("summary", allPass, cpuTime, parseFailures, verificationFailures, timeouts, failMessages);
            outvr.addXmlFiller(pres);
            outvr.toXmlFile(this.outputObject.getFilesystemPath());
            setWasVerificationTimeout(outvr.wasOnlyTimeouts());
            return new VerbSyncWorker(new Fresh());
        }
        
        public override Presentation getRealtimePresentation(Disposition d) {
            if (d is Failed) {
                return base.getRealtimePresentation(d);
            }
            VerificationResult vr = VerificationResult.fromXmlFile(this.outputObject.getFilesystemPath());
            PresentationBuilder pr = new PresentationBuilder();
            pr.startLine();
            pr.color(
                vr.pass ? Presentation.GREEN : Presentation.RED,
                String.Format("{0} {1} {2,1:0.0}s",
                //-getSource().getRelativePath(),
                this.getAbstractIdentifier(),
                (vr.pass ? "Success" : "Fail"), vr.cpuTime));
            pr.endLine();
            if (!vr.pass) {
                foreach (VerificationMessage msg in vr.getMessages()) {
                    pr.pre(msg.message);
                }
            }
            return pr.fix();
        }        

        public override Presentation getPresentation() {
            VerificationResult vr = VerificationResult.fromXmlFile(this.outputObject.getFilesystemPath());
            return vr.presentation;
        }
    }
}

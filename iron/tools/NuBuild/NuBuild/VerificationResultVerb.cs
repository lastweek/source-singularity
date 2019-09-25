using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    abstract class VerificationResultVerb
        : Verb, IRejectable
    {
        public const string VERIFICATION_RESULT_EXTN = ".v";

        protected abstract BuildObject getSource();
        public abstract BuildObject getOutputFile();

        public override Presentation getRealtimePresentation(Disposition d)
        {
            if (d is Failed)
            {
                return base.getRealtimePresentation(d);
            }
            VerificationResult vr = VerificationResult.fromXmlFile(getOutputFile().getFilesystemPath());
            PresentationBuilder pr = new PresentationBuilder();
            pr.startLine();
            pr.color(
                vr.pass ? Presentation.GREEN : Presentation.RED,
                String.Format("{0} {1} {2,5:0.0}s",
                //-getSource().getRelativePath(),
                this.getAbstractIdentifier(),
                (vr.pass ? "Success" : "Fail"), vr.cpuTime));
            pr.endLine();
            if (!vr.pass)
            {
                foreach (VerificationMessage msg in vr.getMessages())
                {
                    pr.pre(msg.message);
                }
            }
            return pr.fix();
        }

        public override Presentation getPresentation()
        {
            VerificationResult vr = VerificationResult.fromXmlFile(getOutputFile().getRelativePath());
            return vr.presentation;
        }

        bool dbgWasVerificationTimeoutRecorded;
        bool wasVerificationTimeout;
        protected void setWasVerificationTimeout(bool value)
        {
            this.dbgWasVerificationTimeoutRecorded = true;
            this.wasVerificationTimeout = value;
        }
        public bool resultWasVerificationTimeout()
        {
            Util.Assert(dbgWasVerificationTimeoutRecorded);
            return wasVerificationTimeout;
        }
    }
}

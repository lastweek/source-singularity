using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Xml;

namespace NuBuild
{
    //-abstract class VerbAsyncWorker : IVerbAsyncWorker
    //-{
    //-    public Disposition disposition;

    //-    public virtual IsSync isSync() { return IsSync.Async; }
    //-    public abstract void runAsync();
    //-    public virtual Disposition complete() { return disposition; }
    //-}

    class VerbSyncWorker : IVerbWorker
    {
        protected Disposition _result;
        public VerbSyncWorker(Disposition result) { this._result = result; }
        public virtual IsSync isSync() { return IsSync.Sync; }
        public void runAsync() { Util.Assert(false); }
        public virtual Disposition complete() { return _result; }
    }

    abstract class Verb
        : IVerb
    {
        public override bool Equals(object obj)
        {
            if (obj is IVerb)
            {
                return getAbstractIdentifier().Equals(((IVerb)obj).getAbstractIdentifier());
            }
            else
            {
                return false;
            }
        }

        public override int GetHashCode()
        {
            return getAbstractIdentifier().GetHashCode();
        }

        public override string ToString()
        {
            return getAbstractIdentifier().ToString();
        }

        public int CompareTo(object other)
        {
            return getAbstractIdentifier().CompareTo(((IVerb)other).getAbstractIdentifier());
        }

        public abstract IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp);
        
        public abstract IEnumerable<IVerb> getVerbs();
        public abstract IEnumerable<BuildObject> getOutputs();
        public virtual BuildObject getDiagnosticsBase()
        {
            return new BuildObject(Path.Combine(
                BuildEngine.theEngine.getObjRoot(), "diagnostics", Util.mungeClean(getAbstractIdentifier().ToString())));
        }
        public virtual IEnumerable<BuildObject> getFailureOutputs()
        {
            return new BuildObject[] {
                getDiagnosticsBase().makeOutputObject(".bat"),
                getDiagnosticsBase().makeOutputObject(".stdout"),
                getDiagnosticsBase().makeOutputObject(".stderr"),
            };
        }

        public abstract IVerbWorker getWorker();

        //- Called by tool when this is the top-level output, it has generated a Fresh
        //- result, and we want to print that result on the display.
        public virtual Presentation getPresentation()
        {
            PresentationBuilder pr = new PresentationBuilder();
            pr.line("Okay.");
            return pr.fix();
        }

        //- Called by tool when we want a short (one-line)
        //- summary for showing in-progress results.
        public virtual Presentation getRealtimePresentation(Disposition d)
        {
            PresentationBuilder pr = new PresentationBuilder();
            pr.startLine();
            pr.color(
                d is Fresh ? Presentation.GREEN : Presentation.RED,
                ToString() + " " + d.ToString());
            pr.endLine();
            if (d is Failed)
            {
                //- This isn't a verification failure, a tool itself broke.
                //- Provide that report.
                foreach (string m in d.getMessages())
                {
                    pr.pre(Presentation.abbreviateLines(m));
                }
            }
            return pr.fix();
        }

        ////////////////////////////////////////////////////
        
        //- Handy helper for verbs using ProcessInvoker.
        bool cpuTimeSecondsValid = false;
        double cpuTimeSeconds;
        public virtual void recordProcessInvokeCpuTime(double cpuTimeSeconds)
        {
            this.cpuTimeSeconds = cpuTimeSeconds;
            this.cpuTimeSecondsValid = true;
        }

        public static string XML_SubprocessTiming = "SubprocessTiming";
        public static string XML_SubprocessTiming_Valid_Attr = "Valid";
        public static string XML_SubprocessTiming_CPUTimeSeconds_Attr = "CPUTimeSeconds";

        public void writeTimingXml(XmlWriter xw)
        {
            xw.WriteStartElement(XML_SubprocessTiming);
            xw.WriteAttributeString(XML_SubprocessTiming_Valid_Attr, cpuTimeSecondsValid.ToString());
            if (cpuTimeSecondsValid)
            {
                xw.WriteAttributeString(XML_SubprocessTiming_CPUTimeSeconds_Attr, cpuTimeSeconds.ToString());
            }
            xw.WriteEndElement();
        }
       
        ////////////////////////////////////////////////////
        
        public abstract AbstractId getAbstractIdentifier();

        public static string XML_DebugVerb = "DebugVerb";
        public static string XML_DebugVerb_Value_Attr = "value";

        public static string XML_DebugDep = "DebugDep";
        public static string XML_DebugDep_Name_Attr = "name";
        public static string XML_DebugDep_Hash_Attr = "hash";
        public void writeDebugXml(XmlWriter xw)
        {
            xw.WriteStartElement(XML_DebugVerb);
            xw.WriteAttributeString(XML_DebugVerb_Value_Attr, getAbstractIdentifier().ToString());
            xw.WriteEndElement();

            DependencyDisposition ddisp;
            foreach (BuildObject obj in getDependencies(out ddisp))
            {
                xw.WriteStartElement(XML_DebugDep);
                xw.WriteAttributeString(XML_DebugDep_Name_Attr, obj.getRelativePath());
                if (!(obj is VirtualBuildObject))
                {
                    xw.WriteAttributeString(XML_DebugDep_Hash_Attr,
                        BuildEngine.theEngine.getHasher().hash(obj.getFilesystemPath()));
                }
                //- TODO: Also write the hash of the file contents, once the interface has stabilized.
                xw.WriteEndElement();
            }
            Util.Assert(ddisp == DependencyDisposition.Complete);
        }
    }

    class ProcessInvokeAsyncWorker : IVerbWorker
    {
        IProcessInvokeAsyncVerb verb;
        string executable;
        string[] args;
        ProcessInvoker.RcHandling rcHandling;
        BuildObject failureBase;
        string finalStdoutPath;
        string dbgText;
        bool allowAbsoluteExe;
        bool allowAbsoluteArgs;
        string workingDir;
        public ProcessInvoker pinv;

        public ProcessInvokeAsyncWorker(
            IProcessInvokeAsyncVerb verb,
            string executable,
            string[] args,
            ProcessInvoker.RcHandling rcHandling,
            BuildObject failureBase,
            string finalStdoutPath = null,
            string dbgText = null,
            bool allowAbsoluteExe = false,
            bool allowAbsoluteArgs = false,
            string workingDir = null)
        {
            this.verb = verb;
            this.executable = executable;
            this.args = args;
            this.rcHandling = rcHandling;
            this.failureBase = failureBase;
            this.finalStdoutPath = finalStdoutPath;
            this.dbgText = dbgText;
            this.allowAbsoluteExe = allowAbsoluteExe;
            this.allowAbsoluteArgs = allowAbsoluteArgs;
            this.workingDir = workingDir;
        }

        public IsSync isSync() { return IsSync.Async; }

        public void runAsync()
        {
            pinv = new ProcessInvoker(
                executable, args, rcHandling, failureBase, finalStdoutPath, dbgText, allowAbsoluteExe, allowAbsoluteArgs, workingDir);
        }

        public Disposition complete() 
        {
            verb.recordProcessInvokeCpuTime(pinv.cpuTime);
            return verb.complete(this);
        }
    }

    interface IProcessInvokeAsyncVerb
    {
        void recordProcessInvokeCpuTime(double cpuTimeSeconds);
        Disposition complete(ProcessInvokeAsyncWorker worker);
    }

}

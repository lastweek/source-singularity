using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class Program
    {
        bool useCloudCache;
        BackgroundWorker backgroundWorker;
        string[] args;
        VerificationRequest verificationRequest = new VerificationRequest();
        bool rejectCachedFailures = false;

        public Program()
        {
            this.useCloudCache = true;
            this.backgroundWorker = new BackgroundWorker();
        }

        static void Main(string[] args)
        {
            new Program().main(args);
            
            
        }

        void usage(string msg)
        {
            Logger.WriteLine(msg);
            Logger.WriteLine(String.Format(
                "Usage: {0} [opts] [Verb Target]*",
                System.AppDomain.CurrentDomain.FriendlyName));
            throw new UserError("Invalid options");
        }

        string ironRoot;
        int jobParallelism = 1;
        List<IVerb> verbs = new List<IVerb>();
        string html_output = null;
        IroncladAppVerb.TARGET target_platform = IroncladAppVerb.TARGET.BARE_METAL;
        DafnyCCVerb.FramePointerMode useFramePointer = DafnyCCVerb.FramePointerMode.NoFramePointer;

        int argi;
        string takeArg(string expectedThing)
        {
            if (argi >= args.Count())
            {
                usage("Expected " + expectedThing);
            }
            string rc = args[argi];
            argi += 1;
            return rc;
        }

        SourcePath conditionSourcePath(string path)
        {
            return new SourcePath(path);
        }

        void fixIronRoot()
        {
            if (ironRoot == null)
            {
                ironRoot = getDefaultIronRoot();
                if (ironRoot == null)
                {
                    usage("--ironRoot not specified and cannot infer ironRoot");
                }
            }
            BuildEngine.theEngine.setIronRoot(ironRoot);
        }

        void parseArgs(string[] args)
        {
            this.args = args;
            argi = 0;
            while (argi<args.Count())
            {
                string next = takeArg("option or verb");    //- should always succeed due to while condition
                if (next.StartsWith("-"))
                {
                    if (next.Equals("--ironRoot"))
                    {
                        if (this.ironRoot != null)
                        {
                            usage("ironRoot set after use");
                        }
                        this.ironRoot = takeArg("value for ironRoot");
                    }
                    else if (next.Equals("-j") || next.Equals("--jobs"))
                    {
                        this.jobParallelism = Int32.Parse(takeArg("value for jobs"));
                    }
                    else if (next.Equals("--localcache"))
                    {
                        BuildEngine.theEngine.setLocalCache(takeArg("path for localcache"));
                    }
                    else if (next.ToLower().Equals("--cloudcache"))
                    {
                        this.useCloudCache = true;
                    }
                    else if (next.ToLower().Equals("--no-cloudcache"))
                    {
                        this.useCloudCache = false;
                    }
                    else if (next.ToLower().Equals("--verify"))
                    {
                        this.verificationRequest.verifyMode = VerificationRequest.VerifyMode.Verify;
                    }
                    else if (next.ToLower().Equals("--no-verify"))
                    {
                        this.verificationRequest.verifyMode = VerificationRequest.VerifyMode.NoVerify;
                    }
                    else if (next.ToLower().Equals("--no-symdiff"))
                    {
                        this.verificationRequest.verifyMode = VerificationRequest.VerifyMode.NoSymDiff;
                    }
                    else if (next.ToLower().Equals("--verify-select"))
                    {
                        this.verificationRequest.verifyMode = VerificationRequest.VerifyMode.SelectiveVerify;
                        this.verificationRequest.selectiveVerifyModuleNames.Add(takeArg("filename for selective-verify"));
                    }
                    else if (next.ToLower().Equals("--html"))
                    {
                        this.html_output = takeArg("filename for html report");
                    } 
                    else if (next.ToLower().Equals("--windows")) 
                    {
                        this.target_platform = IroncladAppVerb.TARGET.WINDOWS;
                    } 
                    else if (next.ToLower().Equals("--useframepointer")) 
                    {
                        this.useFramePointer = DafnyCCVerb.FramePointerMode.UseFramePointer;
                    }
                    else if (next.ToLower().Equals("--reject-cached-failures"))
                    {
                        this.rejectCachedFailures = true;
                    }
                    else
                    {
                        usage("unrecognized option " + next);
                    }
                }
                else
                {
                    string verb = next;
                    string target = takeArg("verb-target");

                    fixIronRoot();
                    if (verb.Equals("DafnyVerifyTree"))
                    {
                        verbs.Add(new VerificationResultSummaryVerb(new DafnyVerifyTreeVerb(conditionSourcePath(target))));
                    } 
                    else if (verb.Equals("BatchDafny")) 
                    {
                        if (!target.EndsWith(".batch")) {
                            usage("Batching expects a .batch file containing a list of .dfy files");
                        }
                        verbs.Add(new VerificationResultSummaryVerb(new BatchVerifyVerb(conditionSourcePath(target), BatchVerifyVerb.BatchMode.DAFNY, verificationRequest, useFramePointer)));
                    } 
                    else if (verb.Equals("BatchApps")) 
                    {
                        if (!target.EndsWith(".batch")) {
                            usage("Batching expects a .batch file containing a list of .dfy files");
                        }
                        verbs.Add(new VerificationResultSummaryVerb(new BatchVerifyVerb(conditionSourcePath(target), BatchVerifyVerb.BatchMode.APP, verificationRequest, useFramePointer)));
                    }
                    else if (verb.Equals("Beat"))
                    {
                        verbs.Add(new BeatVerb(BuildEngine.theEngine.getVerveContextVerb(PoundDefines.empty()), conditionSourcePath(target), appLabel:null));
                    }
                    else if (verb.Equals("Boogie"))
                    {
                        verbs.Add(new BoogieVerb(BuildEngine.theEngine.getVerveContextVerb(PoundDefines.empty()), conditionSourcePath(target), symdiff: verificationRequest.getSymDiffMode()));
                    }
                    else if (verb.Equals("IroncladApp"))
                    {
                        verbs.Add(new IroncladAppVerb(conditionSourcePath(target), target_platform, this.useFramePointer, verificationRequest));
                    }
                    else if (verb.Equals("VSSolution"))
                    {
                        verbs.Add(new VSSolutionVerb(new SourcePath(target, SourcePath.SourceType.sourceTypeTools)));
                    }
                    else if (verb.Equals("nmake"))
                    {
                        verbs.Add(new NmakeVerb(new SourcePath(target, SourcePath.SourceType.sourceTypeTools)));
                    } 
                    else if (verb.Equals("BootableApp")) 
                    {
                        verbs.Add(new BootableAppVerb(conditionSourcePath(target), this.useFramePointer, verificationRequest));
                    }
                    else
                    {
                        usage("Unknown verb " + verb);
                    }
                }
            }

            fixIronRoot();
        }

        private IItemCache GetItemCache()
        {
            string localCacheDirectory = Path.Combine(
                BuildEngine.theEngine.getIronRoot(),
                BuildEngine.theEngine.getLocalCache());

            if (this.useCloudCache)
            {
                try
                {
                    return new ItemCacheMultiplexer(
                        new ItemCacheLocal(localCacheDirectory),
                        new ItemCacheCloud(),
                        this.backgroundWorker);
                }
                catch (Microsoft.WindowsAzure.Storage.StorageException)
                {
                    //- -
                    //- This will handle the case of being disconnected
                    //- at NuBuild launch time.
                    //- -
                    Logger.WriteLine("Failed to create multiplexed cloud cache -- falling back to just local cache.");
                }
            }

            return new ItemCacheLocal(localCacheDirectory);
        }

        const string IRONROOT_sentinel = "IRONROOT.sentinel";
        string getAssemblyPath()
        {
            string assyUri = System.Reflection.Assembly.GetExecutingAssembly().CodeBase;
            string assyPath = new Uri(assyUri).LocalPath;
            return assyPath;
        }
        string getDefaultIronRoot()
        {
            string exepath = Path.GetDirectoryName(getAssemblyPath());
            exepath = Path.GetFullPath(exepath);
            string[] parts = exepath.Split(new Char[] { '\\' });
            for (int i = parts.Length; i > 0; i--)
            {
                string proposal = String.Join("\\", parts.Take(i));
                if (File.Exists(Path.Combine(proposal, IRONROOT_sentinel)))
                {
                    return proposal;
                }
            }
            return null;
        }

        void logNubuildInvocation(string[] args)
        {
            Logger.WriteLine(String.Format("{0} {1}",
                getAssemblyPath(),
                String.Join(" ", args)));
        }

        //- NB this file is found in the default ironroot, since we
        //- grab it before we parse your --ironroot argument.
        private const string NUBUILD_CONFIG = "nubuild.config";
        private IEnumerable<string> fetchConfigArgs()
        {
            string config_path =
                Path.Combine(getDefaultIronRoot(), NUBUILD_CONFIG);
            if (!File.Exists(config_path))
            {
                return new string[] {};
            }
            List<string> config_args = new List<string>();
            foreach (string line in File.ReadAllLines(config_path))
            {
                foreach (string word in line.Trim().Split(new char[] { ' ' }))
                {
                    config_args.Add(word);
                }
            }
            return config_args;
        }

        void main(string[] cmdline_args)
        {
            string[] all_args = fetchConfigArgs().Concat(cmdline_args).ToArray();
            logNubuildInvocation(all_args);
            try
            {
                parseArgs(all_args);
            }
            catch (UserError err)
            {
                usage(err.Message);
            }

            Scheduler scheduler = new Scheduler(jobParallelism, GetItemCache(), rejectCachedFailures);
            scheduler.addTargetVerbs(verbs);

            
            
                scheduler.parallelSchedule();
            
            
            
            
            
            

            IEnumerable<BuildObject> targets = scheduler.getTargets();

            BuildObject outputTarget = null;
            if (targets.Count() > 0)
            {
                outputTarget = targets.First();
            }
            else
            {
                Logger.WriteLine("No targets requested.");
            }
            if (targets.Count() > 1)
            {
                //- TODO need a better story for relaying failure results. Right now
                //- they get stuck in the results cache, but don't appear where we
                //- can find them. Emit to a log, or to files in nuobj?
                Logger.WriteLine("Multiple targets build. First result follows.");
            }
            if (outputTarget!=null)
            {
                Disposition d = scheduler.getObjectDisposition(outputTarget);
                if (d is Fresh)
                {
                    ASCIIPresentater ascii = new ASCIIPresentater();
                    IVerb verb = scheduler.getParent(outputTarget);
                    verb.getPresentation().format(ascii);
                    Logger.Write(ascii.ToString());

                    if (this.html_output != null)
                    {
                        HTMLPresentater html = new HTMLPresentater();
                        verb.getPresentation().format(html);

                        try
                        {
                            using (StreamWriter sw = new StreamWriter(this.html_output))
                            {
                                sw.Write(html.ToString());
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.WriteLine("Failed to write html output to file: " + html_output);
                            Logger.WriteLine("Exception was: " + e);
                        }
                    }
                }
                else
                {
                    Logger.WriteLine("Build failed.");
                    foreach (string msg in d.getMessages())
                    {
                        Logger.Write(msg);
                    }
                }
            }
            else if (targets.Count() == 0)
            {
                Logger.WriteLine("No targets requested.");
            }
            else
            {
                Logger.WriteLine("Multiple targets built. Look for results in nuobj/.");
            }

            //- -
            //- We have to explicitly ask the BackgroundWorker thread to exit
            //- as it will prevent the process from exiting until it does.
            //- -
            this.backgroundWorker.StopWork();

            //- -
            //- Report what the background worker accomplished during this run.
            //- -
            this.backgroundWorker.WaitForCompletion();
            Logger.WriteLine(String.Format("Background Worker completed {0} work items out of {1} queued.",
                this.backgroundWorker.GetWorkItemsPerformed,
                this.backgroundWorker.GetWorkItemsQueued));
            if (this.backgroundWorker.GetWorkItemsFailed != 0)
            {
                Logger.WriteLine(String.Format(
                    "{0} work item procedures failed (threw an exception).",
                    this.backgroundWorker.GetWorkItemsFailed));
            }
        }
    }
}

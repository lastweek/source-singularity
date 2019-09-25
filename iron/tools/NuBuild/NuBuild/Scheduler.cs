using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;
using System.IO;
using System.Security.Cryptography;
using System.Runtime.Remoting.Metadata.W3cXsd2001;

namespace NuBuild
{
    class Scheduler
    {
        VerbToposorter verbToposorter;
        const string dispositionFileExtension = ".disp";
        HashSet<BuildObject> targets;
        WaitIndex waitIndex;
        ResultCache resultCache;
        NuObjContents nuObjContents;
        DependencyCache depCache;

        //-DbgVerbCounter dbgVerbCounter = new DbgVerbCounter();
        
        //- These verbs have been submitted for exeuction or failed,
        //- and need not be further considered.
        HashSet<IVerb> resolvedVerbs;
        //- These verbs have been completed, and hence can't contribute
        //- to resolving any pending dependencies.
        //- (If it's resolved and not completed, it must be submitted
        //- for asynchronous execution.)
        HashSet<IVerb> completedVerbs;
        
        //- Our general strategy is to record the outcome of every verb in
        //- a persistent result cache, and then to evaluate each downstream
        //- BuildObject by querying that cache. But when one verb fails,
        //- it may make the downstream verb unable to even compute its input
        //- set, and hence its concreteIdentifier (the key to a persistent
        //- cache). If we don't record the outcome somehow, we'll loop
        //- forever trying to learn the outcome of the downstream failure.
        //- So we record it here in-process, keyed by abstractIdentifier
        //- (which is assumed to be stable over a single run of NuBuild).
        //- Invariant: all values in this dictionary are Faileds. (We store
        //- them because they might (someday) propagate information about
        //- what failed for an error message.)
        Dictionary<IVerb,Disposition> unrecordableFailures;

        IHasher hasher;
        AsyncRunner asyncRunner;
        internal const bool debug = false;
        bool rejectCachedFailures;

        public Scheduler(int jobParallelism, IItemCache itemCache, bool rejectCachedFailures)
        {
            targets = new HashSet<BuildObject>();
            waitIndex = new WaitIndex();
            nuObjContents = BuildEngine.theEngine.getNuObjContents();
            resultCache = new ResultCache(itemCache, nuObjContents);
            unrecordableFailures = new Dictionary<IVerb, Disposition>();
            this.hasher = BuildEngine.theEngine.getHasher();
            verbToposorter = new VerbToposorter(hasher);
            asyncRunner = new AsyncRunner(verbToposorter, jobParallelism);
            resolvedVerbs = new HashSet<IVerb>();
            completedVerbs = new HashSet<IVerb>();
            depCache = new DependencyCache();
            this.rejectCachedFailures = rejectCachedFailures;
        }

        public void addTargets(IEnumerable<BuildObject> newTargets)
        {
            targets.UnionWith(newTargets);
        }

        string dispositionFilePath(BuildObject bob)
        {
            return bob.getFilesystemPath() + dispositionFileExtension;
        }

        string computeInputHash(IVerb verb, bool assertHashAvailable)
        {
            StringBuilder sb = new StringBuilder();
            sb.Append(verb.getAbstractIdentifier().getConcreteId());
            DependencyDisposition ddisp;
            foreach (BuildObject obj in depCache.getDependencies(verb, out ddisp))
            {
                sb.Append(",");
                string hash = resultCache.getKnownObjectHash(obj);
                Util.Assert(!assertHashAvailable || (hash != null));
                sb.Append(hash);
            }
            if (ddisp == DependencyDisposition.Failed)
            {
                //- This happens when we're trying to markFailed,
                //- but the upstream has failed and we can't compute
                //- our dependencies. In that case, markFailed
                //- settles for noting the failure in-process,
                //- but not caching the result. (Okay, since this
                //- failure propagation is cheap to rediscover.)
                Util.Assert(!assertHashAvailable);
                return null;
            }
            Util.Assert(ddisp == DependencyDisposition.Complete);
            string rc = Util.hashString(sb.ToString());
            return rc;
        }
 
        void prepareObjDirectory(IVerb verb)
        {
            foreach (BuildObject obj in verb.getOutputs())
            {
                obj.prepareObjDirectory();
            }
        }

        private HashSet<IVerb> requiredVerbs;
        private HashSet<IVerb> nextVerbs;

        //- Find some parents that could possibly complete in the future and help
        //- resolve one of these deps.
        private List<IVerb> robustDiscoverReadyDeps(IEnumerable<BuildObject> staleDeps)
        {
            List<IVerb> newParents = new List<IVerb>();
            foreach (BuildObject dep in staleDeps)
            {
                IVerb parent = hasher.getParent(dep);
                if (parent != null)
                {
                    if (completedVerbs.Contains(parent))
                    {
                        //- Wait, if the parent is completed, why is the child a stale dependency?
                        Util.Assert(false);
                    }
                    newParents.Add(parent);
                }
            }
            return newParents;
        }


        //- Push each potential target somewhere else: replace it with its dependencies, or
        //- mark its outputs failed, or mark it runnable and give it to the async scheduler.
        private int submittedCount;
        private void disposeCurrentVerbs(HashSet<IVerb> currentVerbs)
        {
            submittedCount = 0;
            Say("disposeCurrentVerbs");
            while (currentVerbs.Count() > 0)
            {
                foreach (IVerb verb in currentVerbs)
                {
                    Say("disposeCurrentVerbs considering " + verb);
                    //-dbgVerbCounter.consider(verb, DbgVerbCounter.DbgVerbCondition.DVWake);

                    if (resolvedVerbs.Contains(verb))
                    {
                        //- enthusiastic wakeup?
                        continue;
                    }
                    if (waitIndex.isWaiting(verb))
                    {
                        //- He's already waiting for something else.
                        continue;
                    }

                    DependencyDisposition ddisp;
                    List<BuildObject> knownDeps = new List<BuildObject>(depCache.getDependencies(verb, out ddisp));

                    List<BuildObject> staleDeps = new List<BuildObject>();
                    List<BuildObject> failedDeps = new List<BuildObject>();
                    foreach (BuildObject dep in knownDeps)
                    {
                        Disposition disp = nuObjContents.getDisposition(dep);
                        if (disp is Stale)
                        { staleDeps.Add(dep); }
                        else if (disp is Failed)
                        { failedDeps.Add(dep);  }
                    }

                    if (staleDeps.Count() > 0 || ddisp==DependencyDisposition.Incomplete)
                    {
                        //- some inputs aren't yet available, so we can prompt one of those verbs
                        //- instead, and wake this one up when those are done.
                        Util.Assert(staleDeps.Count() > 0);

                        List<IVerb> newParents = robustDiscoverReadyDeps(staleDeps);
                        if (newParents.Count() == 0)
                        {
                            reexamineVerb(verb);
                            newParents = robustDiscoverReadyDeps(staleDeps);
                            Util.Assert(newParents.Count() > 0);
                        }
                        nextVerbs.UnionWith(newParents);
                        Say(String.Format("disposeCurrentVerbs waits {0}   dependent on {1}   liberating {2}",
                            verb,
                            String.Join(",", staleDeps),
                            String.Join(",", newParents)));
                        waitIndex.insert(verb, staleDeps);
                    }
                    else if (ddisp == DependencyDisposition.Failed || failedDeps.Count() > 0)
                    {
                        Say(String.Format("disposeCurrentVerbs marks {0} failed", verb));
                        markFailed(verb);
                        resolvedVerbs.Add(verb);
                        //-dbgVerbCounter.consider(verb, DbgVerbCounter.DbgVerbCondition.DVDepsNonstale);
                    }
                    else
                    {
                        //- all inputs are available, so we can compute concrete identifier
                        //- to retrieve from cache...
                        string inputHash = computeInputHash(verb, true);
                        Util.Assert(inputHash != null);

                        if (!fetchFromCache(verb, inputHash))
                        {
                            //-if (verb is BoogieAsmVerificationObligationListVerb) { System.Environment.Exit(0); }
                            Say(String.Format("disposeCurrentVerbs submits {0}", verb));
                            //- or if it's not in cache, we can execute.
                            prepareObjDirectory(verb);
                            //- verb's inputs are ready, and output is stale: mark verb runnable
                            //-Say(String.Format("  {0} submitted", verb));
                            asyncRunner.submitVerb(verb);
                            submittedCount += 1;
                        }
                        resolvedVerbs.Add(verb);
                        //-dbgVerbCounter.consider(verb, DbgVerbCounter.DbgVerbCondition.DVDepsNonstale);
                    }
                }
                //- We've disposed all the current verbs. But maybe we found some more
                //- we can pop loose right now.
                currentVerbs = nextVerbs;
                nextVerbs = new HashSet<IVerb>();
            }
        }

        private bool fetchFromCache(IVerb verb, string inputHash)
        {
            try
            {
                ResultSummaryRecord summary = resultCache.fetchResult(inputHash);
                if (summary.disposition is Stale)
                {
                    return false;
                }

                if (rejectCachedFailures
                    && (summary.disposition is Failed || summary.isVerificationTimeout))
                {
                    Logger.WriteLine(String.Format(
                        "NOTE: rejecting failure from cache {0}", verb));
                    return false;
                }

                Say(String.Format("disposeCurrentVerbs pulls {0} from cache", verb));
                //- Hey, this verb is already computed! Nothing to do.
                //- Bring the objects into nuobj where the user can see
                //- them -- and where we can explore them for dependency evaluation.
                resultCache.fetchOutputObjects(verb, summary.outputs, summary.disposition);

                verbIsComplete(verb, summary.disposition, BlessingRequest.NoBless);

                return true;
            }
            catch (ObjectMissingFromCacheException ex)
            {
                Logger.WriteLine(String.Format(
                    "WARNING: expected object {0} missing from cache; discarding cached result {1}",
                    ex,
                    verb));
                return false;
            }
        }

        public void dbgDisplayCounts()
        {
            //-dbgVerbCounter.dbgDisplayCounts();
            depCache.dbgPrintStats();
        }

        private void reexamineVerb(IVerb verb)
        {
            //- Perhaps this child knows more since we last tried
            //- to work upstream from it.
            foreach (IVerb parentVerb in verb.getVerbs())
            {
                hasher.addVerb(parentVerb);
            }
        }

        private void processTaskCompletions(List<AsyncRunner.TaskCompletion> taskCompletions)
        {
            foreach (AsyncRunner.TaskCompletion tc in taskCompletions)
            {
                //- We may record a Failure if the verb didn't output
                //- everything it promised to.
                Disposition recordedDisposition = recordResult(tc.verb, tc.disposition);

                Say(String.Format("  {0} completed with disposition {1}", tc.verb, tc.disposition));
            }
            //- Waking process may have shaken some verbs loose for us to evaluate next time around.
        }

        public void parallelSchedule()
        {
            requiredVerbs = new HashSet<IVerb>();
            foreach (BuildObject target in targets)
            {
                requiredVerbs.Add(hasher.getParent(target));
            }

            //- The set we're evaluating now.
            HashSet<IVerb> currentVerbs = new HashSet<IVerb>(requiredVerbs);
            //- A set into which we accumulate verbs to evaluate on the next pass.
            nextVerbs = new HashSet<IVerb>();

            while (requiredVerbs.Count()>0)
            {
                disposeCurrentVerbs(currentVerbs);
                currentVerbs = null;    //- just to be obvious.
                
                //- Okay, now we wait around for some deps to finish, freeing up new targets.
                while (nextVerbs.Count()==0 && requiredVerbs.Count()>0)
                {
                    Say(String.Format("scheduler waits, having submitted {0} verbs", submittedCount));
                    //-Util.Assert(submittedCount > 0);  

                    List<AsyncRunner.TaskCompletion> taskCompletions;
                    taskCompletions = asyncRunner.scheduleAndWait(this);
                    Say("received " + taskCompletions.Count() + " taskCompletions");

                    Util.Assert(requiredVerbs.Count() == 0 || taskCompletions.Count() > 0);
                    processTaskCompletions(taskCompletions);

                    currentVerbs = nextVerbs;
                    nextVerbs = new HashSet<IVerb>();
                    if (currentVerbs.Count() > 0 || requiredVerbs.Count()==0)
                    {
                        //- hey, something changed that we could reschedule on,
                        //- or we're actually all done.
                        break;
                    }
                    //- Hmm, we've got no opportunity to schedule new stuff,
                    //- so the AsyncRunner better not return empty-handed the
                    //- next time through.
                    //- We've got an assert taskCompletions.Count()>0 to check
                    //- for that.
                    Say("Scheduler waiting for more results.");
                }
            }
        }

        internal void dbgDumpWaitIndex()
        {
            waitIndex.dbgDisplayIndex(hasher, this);
        }

        internal string dbgGetVerbStatus(IVerb verb)
        {
            if (completedVerbs.Contains(verb)) { return "completed"; }
            if (resolvedVerbs.Contains(verb)) { return "submitted"; }
            return "pending";
        }

        void Say(string s)
        {
            if (debug)
            {
#pragma warning disable 162
                Logger.WriteLine("[sched] "+s);
#pragma warning restore 162
            }
        }

        void emitRealtimeReport(IVerb verb, Disposition disposition)
        {
            Presentation pr = verb.getRealtimePresentation(disposition);
            ASCIIPresentater ascii = new ASCIIPresentater();
            pr.format(ascii);
            Logger.Write(ascii.ToString());
        }

        enum BlessingRequest { Bless, NoBless };
        void verbIsComplete(IVerb verb, Disposition disp, BlessingRequest blessingRequest)
        {
            emitRealtimeReport(verb, disp);
            
            //-Say(String.Format("  {0} is complete: {1}", verb, dbgDisposition));
            //-if (disp is Failed)
            //-{
            //-    
            //-    
            //-    
            //-    emitRealtimeReport(verb, disp);
            //-}

            //- invariant: all of this verb's objs are non-Stale.
            foreach (BuildObject obj in verb.getOutputs())
            {
                if (blessingRequest == BlessingRequest.Bless)
                {
                    nuObjContents.blessGeneral(obj, disp);
                }
                //-Say(String.Format("  waking {0}", obj));
                IEnumerable<IVerb> wokenSet = waitIndex.awaken(obj);
                //-foreach (IVerb wokenVerb in wokenSet)
                //-{
                //-    
                //-}
                nextVerbs.UnionWith(wokenSet);
            }
            requiredVerbs.Remove(verb);
            completedVerbs.Add(verb);
        }

        Disposition recordResult(IVerb verb, Disposition executionDisposition)
        {
            //- record how each output appeared.

            List<BuildObjectValuePointer> outputs = new List<BuildObjectValuePointer>();
            List<string> missingOutputs = new List<string>();
            IEnumerable<BuildObject> expectedOutputs = verb.getOutputs();
            if (executionDisposition is Failed)
            {
                expectedOutputs = expectedOutputs.Concat(verb.getFailureOutputs());
            }
            bool hasVirtualOutputs = false;
            foreach (BuildObject outobj in expectedOutputs)
            {
                if (!(outobj is VirtualBuildObject))
                {
                    if (File.Exists(outobj.getFilesystemPath()))
                    {
                        //- Try to catch accidental case mismatches that would burn us when we
                        //- try to fetch the file back in.
                        string fsname = PathNormalizer.dbg_normalizePath_nocache(outobj.getFilesystemPath(), false);
                        Util.Assert(Path.GetFileName(fsname).Equals(outobj.getFileName()));

                        outputs.Add(resultCache.storeObject(outobj));
                    }
                    else
                    {
                        missingOutputs.Add(String.Format("Missing expected output {0}", outobj.getRelativePath()));
                    }
                }
                else
                {
                    hasVirtualOutputs = true;
                    if (nuObjContents.getDisposition(outobj) is Fresh)
                    {
                        //- nothing to cache; virtual objects only survive in nuObjContents, the in-process cache
                    }
                    else
                    {
                        missingOutputs.Add(String.Format("Missing expected virtual {0}", outobj.getRelativePath()));
                    }
                }
            }
            if (!(executionDisposition is Failed) && missingOutputs.Count() > 0)
            {
                executionDisposition = new Failed(missingOutputs);
            }
            ResultSummaryRecord summary = new ResultSummaryRecord(verb, executionDisposition, outputs);
            string inputHash = computeInputHash(verb, true);
            Util.Assert(inputHash != null);
            if (!hasVirtualOutputs)
            {
                resultCache.storeResult(inputHash, summary);
            }
            else
            {
                Say("Not caching verb persistently: " + verb);
            }

            verbIsComplete(verb, executionDisposition, BlessingRequest.Bless);
            return executionDisposition;
        }

        void markFailed(IVerb verb)
        {
            //- at least one of verb's inputs has a permanent failure, so we didn't
            //- even try to execute it.
            Disposition disposition = new Failed("upstream failure");
            ResultSummaryRecord summary = new ResultSummaryRecord(verb, disposition, new BuildObjectValuePointer[] {});
            
            //- NB never store upstream failures to the persistent cache, because
            //- they depend on our knowledge this run that the upstream verb failed.
            //- If, in another run, the verb or its inputs are modified, produce the
            //- same outputs, but returns success, we'll be stuck pulling this
            //- upstream failure out of cache but calling this verb a failure.
            //-string inputHash = computeInputHash(verb, false);
            //-if (inputHash != null)
            //-{
            //-    Util.Assert(false);
            //-    
            //-    
            //-    
            //-    
            //-    
            //-    resultCache.storeResult(inputHash, summary);
            //-}
            //-else
            //-{
                unrecordableFailures[verb] = disposition;
            //-}
            verbIsComplete(verb, disposition, BlessingRequest.Bless);
        }

        internal void addVerb(IVerb verb)
        {
            verbToposorter.addVerb(verb);
        }

        internal void addTargetVerbs(List<IVerb> verbs)
        {
            foreach (IVerb verb in verbs)
            {
                addVerb(verb);
                addTargets(verb.getOutputs());
            }
        }

        internal IEnumerable<BuildObject> getTargets()
        {
            return targets;
        }

        internal IVerb getParent(BuildObject obj)
        {
            return hasher.getParent(obj);
        }

        internal Disposition getObjectDisposition(BuildObject obj)
        {
            return nuObjContents.getDisposition(obj);
        }

        private const string DBG_PROGRESS = "nubuild.progress";
        internal void dbgUpdateProgress(int runnableVerbsCount, int runningVerbsCount)
        {
            StringBuilder sb = new StringBuilder();
            sb.AppendLine("completedVerbs: "+completedVerbs.Count());
            sb.AppendLine("resolvedVerbs:  " + resolvedVerbs.Count());
            sb.AppendLine("runnableVerbs:  " + runnableVerbsCount);
            sb.AppendLine("runningVerbs:   " + runningVerbsCount);
            sb.AppendLine("waitingVerbs:   " + waitIndex.Count());
            File.WriteAllText(DBG_PROGRESS, sb.ToString());
        }
    }
}

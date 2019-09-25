using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class WaitIndex
    {
        class WaitRecord
        {
            public IVerb verb;
            public IEnumerable<BuildObject> knownDeps;
            public WaitRecord(IVerb verb, IEnumerable<BuildObject> knownDeps)
            {
                this.verb = verb;
                this.knownDeps = knownDeps;
            }
        }

        Dictionary<IVerb,WaitRecord> waitingVerbs;
        Dictionary<BuildObject, HashSet<WaitRecord>> fwdDeps;

        public WaitIndex()
        {
            waitingVerbs = new Dictionary<IVerb, WaitRecord>();
            fwdDeps = new Dictionary<BuildObject, HashSet<WaitRecord>>();
        }

        internal void insert(IVerb verb, IEnumerable<BuildObject> knownDeps)
        {
            //- insert one fwd pointer for each obj verb is already known to
            //- depend upon. The fact that this verb is waiting implies that
            //- one of these deps is stale here and needs built/fetched.
            WaitRecord waitRecord = new WaitRecord(verb, knownDeps);
            foreach (BuildObject dep in knownDeps)
            {
                if (!fwdDeps.ContainsKey(dep))
                {
                    fwdDeps.Add(dep, new HashSet<WaitRecord>());
                }
                fwdDeps[dep].Add(waitRecord);
            }
            waitingVerbs.Add(verb, waitRecord);
            Say("sleeps " + verb);
        }

        public int Count()
        {
            return waitingVerbs.Count;
        }

        void Say(string msg)
        {
            //-Logger.WriteLine("[wtidx] " + msg);
        }

        //- Remove any verb with obj in its dependency set.
        internal IEnumerable<IVerb> awaken(BuildObject obj)
        {
            Say("awaken " + obj);
            HashSet<WaitRecord> wokenRecords;
            HashSet<IVerb> result = new HashSet<IVerb>();
            if (fwdDeps.ContainsKey(obj))
            {
                wokenRecords = fwdDeps[obj];
                fwdDeps.Remove(obj);

                //- Remove all the other index pointers for each removed verb
                foreach (WaitRecord waitRecord in wokenRecords)
                {
                    foreach (BuildObject dep in waitRecord.knownDeps)
                    {
                        if (fwdDeps.ContainsKey(dep))
                        {
                            fwdDeps[dep].Remove(waitRecord);
                        }
                    }
                    result.Add(waitRecord.verb);
                    waitingVerbs.Remove(waitRecord.verb);
                    Say("  wakes " + waitRecord.verb);
                }
            } else {
                result = new HashSet<IVerb>();
            }
            return result;
        }

        internal bool isWaiting(IVerb verb)
        {
            return waitingVerbs.ContainsKey(verb);
        }

        public void dbgDisplayIndex(IHasher hasher, Scheduler dbgScheduler)
        {
            List<WaitRecord> waitRecords = new List<WaitRecord>(waitingVerbs.Values);
            for (int i = 0; i < waitRecords.Count(); i++)
            {
                WaitRecord wr = waitRecords[i];
                List<int> depNums = new List<int>();
                List<BuildObject> unknownDeps = new List<BuildObject>();
                List<string> unscheduledDeps = new List<string>();
                foreach (BuildObject dep in wr.knownDeps)
                {
                    IVerb depOnVerb = hasher.getParent(dep);
                    if (depOnVerb==null)
                    {
                        unknownDeps.Add(dep);
                    }
                    else if (!waitingVerbs.ContainsKey(depOnVerb))
                    {
                        unscheduledDeps.Add(String.Format("{0} waiting on {1} {2}",
                            dep, depOnVerb,
                            dbgScheduler.dbgGetVerbStatus(depOnVerb)));
                    }
                    else
                    {
                        WaitRecord depWr = waitingVerbs[depOnVerb];
                        depNums.Add(waitRecords.IndexOf(depWr));
                    }
                }
                Logger.WriteLine(String.Format("{0}. {1} waits on ({2}), {3} unknown, {4} unscheduled",
                    i, wr.verb, String.Join(",", depNums), unknownDeps.Count(), unscheduledDeps.Count()));
                dbgPreview("Unknown", unknownDeps.Select(it => it.ToString()), 3);
                dbgPreview("Unscheduled", unscheduledDeps, 20);
            }
        }
        private void dbgPreview(string s, IEnumerable<string> items, int max)
        {
            int i=0;
            foreach (string o in items)
            {
                Logger.WriteLine(String.Format("  {0} {1}/{2} {3}",
                    s, i, items.Count(), o));
                i+=1;
                if (i == max) { break; }
            }
        }
    }
}

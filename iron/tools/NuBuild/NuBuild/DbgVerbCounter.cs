using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    //- I used this class to determine how much effort we were wasting
    //- re-computing verb.getDependencies
    class DbgVerbCounter
    {
        public enum DbgVerbCondition { DVWake, DVDepsIncomplete, DVDepsStale, DVDepsNonstale, DVTotal }
        Dictionary<Tuple<IVerb, DbgVerbCondition>, int> dbgCounts = new Dictionary<Tuple<IVerb, DbgVerbCondition>, int>();
        public void consider(IVerb verb, DbgVerbCondition cond)
        {
            consider_inner(new Tuple<IVerb, DbgVerbCondition>(verb, cond));
            consider_inner(new Tuple<IVerb, DbgVerbCondition>(verb, DbgVerbCondition.DVTotal));
        }
        void consider_inner(Tuple<IVerb, DbgVerbCondition> key)
        {
            if (!dbgCounts.ContainsKey(key))
            {
                dbgCounts[key] = 0;
            }
            dbgCounts[key] += 1;
        }
        public void dbgDisplayCounts()
        {
            List<Tuple<IVerb, DbgVerbCondition>> keys = new List<Tuple<IVerb, DbgVerbCondition>>(dbgCounts.Keys);
            keys.Sort();
            foreach (Tuple<IVerb, DbgVerbCondition> key in keys)
            {
                Logger.WriteLine(String.Format("{0:20}: {1}", key, dbgCounts[key]));
            }
        }

    }
}

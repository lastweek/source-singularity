using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class DependencyCache
    {
        class DependencyResult
        {
            public IEnumerable<BuildObject> deps;
            public DependencyDisposition ddisp;
        }
        Dictionary<IVerb, DependencyResult> theCache;
        int dbgQueries = 0;
        int dbgMisses = 0;

        public DependencyCache()
        {
            theCache = new Dictionary<IVerb, DependencyResult>();
        }

        public IEnumerable<BuildObject> getDependencies(IVerb verb, out DependencyDisposition ddisp)
        {
            dbgQueries += 1;
            DependencyResult result;
            bool present = theCache.TryGetValue(verb, out result);
            if (!present)
            {
                dbgMisses += 1;
                result = new DependencyResult();
                result.deps = verb.getDependencies(out result.ddisp);
                if (result.ddisp != DependencyDisposition.Incomplete)
                {
                    //- Can't cache incomplete results, since they may change upon
                    //- later inspection.
                    theCache[verb] = result;
                }
            }
            ddisp = result.ddisp;
            return result.deps;
        }

        public void dbgPrintStats()
        {
            Logger.WriteLine(String.Format(
                "DependencyCache queries {0} misses {1}", dbgQueries, dbgMisses));
        }
    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;

namespace NuBuild
{
    class VerbToposorter
        : IComparer<IVerb>
    {
        IHasher hasher;
        HashSet<IVerb> knownVerbs;

        Dictionary<IVerb, int> verbDepth;

        public VerbToposorter(IHasher hasher)
        {
            this.hasher = hasher;
            knownVerbs = new HashSet<IVerb>();
            verbDepth = new Dictionary<IVerb, int>();
        }

        public int getDepth(IVerb verb)
        {
            if (verbDepth.ContainsKey(verb))
            {
                return verbDepth[verb];
            }

            int depth;
            if (verb is DafnyVerifyOneVerb)
            {
                DafnyVerifyOneVerb vone = (DafnyVerifyOneVerb)verb;
                int deepestParent = -1;
                foreach (SourcePath sourcePath in vone.getDirectIncludes())
                {
                    IVerb parent = new DafnyVerifyOneVerb(sourcePath);
                    int parentDepth = getDepth(parent);
                    deepestParent = Math.Max(deepestParent, parentDepth);
                }
                depth = deepestParent + 1;
            }
            else
            {
                //- Right now we only care about ordering the DafnyVerifyOneVerbs
                //- wrt one another. Other verbs will be constrained by build
                //- dependency anyway.
                depth = 0;
            }
            verbDepth[verb] = depth;
            return depth;
        }

        public void addVerb(IVerb verb)
        {
            if (knownVerbs.Contains(verb))
            {
                return;
            }
            knownVerbs.Add(verb);
            hasher.addVerb(verb);

            //- All verbs are added recursively, so that we have a complete index
            //- of outputs back to the verbs that generate them.
            addVerbs(verb.getVerbs());
        }

        public void addVerbs(IEnumerable<IVerb> availableVerbs)
        {
            foreach (IVerb verb in availableVerbs)
            {
                addVerb(verb);
            }
        }

        public int Compare(IVerb x, IVerb y)
        {
            int rc;
            int c0 = getDepth(x) - getDepth(y);
            if (c0 != 0)
            {
                rc = c0;
            }
            else
            {
                //- break depth ties alphabetically.
                rc = x.ToString().CompareTo(y.ToString());
            }
            //-Logger.WriteLine(String.Format("Compare({0},{1})=={2}", x, y, rc));
            return rc;
        }
    }
}

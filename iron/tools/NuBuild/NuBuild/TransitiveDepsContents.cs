using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class TransitiveDepsContents : VirtualContents
    {
        OrderPreservingSet<BuildObject> _shallowDeps, _transitiveDeps;
        public IEnumerable<BuildObject> shallowDeps { get { return _shallowDeps; } }
        public IEnumerable<BuildObject> transitiveDeps { get { return _transitiveDeps; } }
        public TransitiveDepsContents(OrderPreservingSet<BuildObject> shallowDeps, OrderPreservingSet<BuildObject> transitiveDeps)
        {
            _shallowDeps = shallowDeps;
            _transitiveDeps = transitiveDeps;
        }

        //-public override string getConcreteSummary()
        //-{
        //-    return "(" + String.Join(",", transitiveDeps) + ")";
        //-}
    }
}

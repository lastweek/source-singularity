using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class DafnyTransitiveDepsVerb
        : TransitiveDepsVerb
    {
        public DafnyTransitiveDepsVerb(BuildObject input)
            : base(input)
        {
        }

        protected override TransitiveDepsVerb factory(BuildObject obj)
        {
            return new DafnyTransitiveDepsVerb(obj);
        }

        protected override IIncludeFactory getIncludeFactory()
        {
            return new DafnyIncludes();
        }

    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class BasmTransitiveDepsVerb
        : TransitiveDepsVerb
    {
        IContextGeneratingVerb contextVerb;

        public BasmTransitiveDepsVerb(IContextGeneratingVerb contextVerb, BuildObject input)
            : base(input)
        {
            this.contextVerb = contextVerb;
        }

        protected override TransitiveDepsVerb factory(BuildObject obj)
        {
            return new BasmTransitiveDepsVerb(contextVerb, obj);
        }

        protected override void extendDeps(List<BuildObject> deps)
        {
            deps.Add(contextVerb.getContextOutput());
        }

        protected override IIncludeFactory getIncludeFactory()
        {
            ContextContents context = (ContextContents)
                BuildEngine.theEngine.getNuObjContents().openVirtual(contextVerb.getContextOutput());
            return new BasmObligationIncludes(context.context);
        }
    }
}

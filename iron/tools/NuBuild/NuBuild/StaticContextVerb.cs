using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    //- Recipient needs to accept IContextGeneratingVerbs, but we don't need
    //- any dependencies to produce this (static) context. So this is a simple,
    //- non-dependent verb that just spews a ContextContents.
    class StaticContextVerb
        : ContextGeneratingVerb
    {
        IIncludePathContext _context;

        public StaticContextVerb(IIncludePathContext context, string nickname, PoundDefines poundDefines)
            : base(nickname, poundDefines)
        {
            this._context = context;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return new BuildObject[] { };
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { };
        }

        public override IVerbWorker getWorker()
        {
            NuObjContents noc = BuildEngine.theEngine.getNuObjContents();
            ContextContents contents = new ContextContents(_context);
            BuildEngine.theEngine.getNuObjContents().storeVirtual(getContextOutput(), new Fresh(), contents);
            return new VerbSyncWorker(new Fresh());
        }
    }
}


using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class ConcatContextVerb
        : ContextGeneratingVerb
    {
        List<IContextGeneratingVerb> _parents;

        public ConcatContextVerb(IEnumerable<IContextGeneratingVerb> parents, PoundDefines poundDefines)
            : base("Cat("+String.Join(",", parents)+")", poundDefines)
        {
            _parents = new List<IContextGeneratingVerb>(parents);
        }

        public ConcatContextVerb(IContextGeneratingVerb parentA, IContextGeneratingVerb parentB, PoundDefines poundDefines)
            : this(new IContextGeneratingVerb[] { parentA, parentB }, poundDefines)
        { }

        public ConcatContextVerb(IContextGeneratingVerb parentA, IContextGeneratingVerb parentB, IContextGeneratingVerb parentC, PoundDefines poundDefines)
            : this(new IContextGeneratingVerb[] { parentA, parentB, parentC }, poundDefines)
        { }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            return _parents.Select(parent => parent.getContextOutput());
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return _parents;
        }

        public override IVerbWorker getWorker()
        {
            NuObjContents noc = BuildEngine.theEngine.getNuObjContents();
            IEnumerable<IIncludePathContext> contexts = _parents.Select(parent =>
                ((ContextContents)noc.openVirtual(parent.getContextOutput())).context);
            ConcatContext context = new ConcatContext(contexts);
            ContextContents contents = new ContextContents(context);
            BuildEngine.theEngine.getNuObjContents().storeVirtual(getContextOutput(), new Fresh(), contents);
            return new VerbSyncWorker(new Fresh());
        }
    }
}

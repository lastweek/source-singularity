using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    //- This verb waits for a parent verb to complete, then emits
    //- a ContextContents that searches the parent verb's results.
    class VerbOutputsContextVerb
        : ContextGeneratingVerb
    {
        IVerb _parent;
        bool _assertSuspiciousDafnyImpls;

        public VerbOutputsContextVerb(IVerb parent, bool assertSuspiciousDafnyImpls)
            : base(parent.getAbstractIdentifier().ToString(), null)
        {
            this._parent = parent;
            this._assertSuspiciousDafnyImpls = assertSuspiciousDafnyImpls;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;
            //- I really don't care how many outputs the parent has; any one will
            //- link me to the paarent.
            IEnumerable<BuildObject> result = _parent.getOutputs();
            Util.Assert(result.Count() > 0);
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { _parent };
        }

        public override IVerbWorker getWorker()
        {
            VerbOutputsContext context = new VerbOutputsContext(_parent, _assertSuspiciousDafnyImpls);
            ContextContents contents = new ContextContents(context);
            BuildEngine.theEngine.getNuObjContents().storeVirtual(getContextOutput(), new Fresh(), contents);
            return new VerbSyncWorker(new Fresh());
        }
    }
}

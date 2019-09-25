using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    abstract class ContextGeneratingVerb
        : Verb, IContextGeneratingVerb
    {
        public const string CONTEXT_EXTN = ".ctxt";    //- Virtual, so it shouldn't appear in filesystem.
        int version = 1;

        string _nickname;
        PoundDefines _poundDefines;
        BuildObject outputObj;
       
        /
        //- hence hash identity in caches.</param>
        public ContextGeneratingVerb(string nickname, PoundDefines poundDefines)
        {
            this._nickname = nickname;
            this._poundDefines = poundDefines;
        }

        public PoundDefines getPoundDefines()
        {
            return _poundDefines;
        }

        public string getContextIdentifier()
        {
            return _nickname;
        }

        public override AbstractId getAbstractIdentifier()
        {
            return new AbstractId(this.GetType().Name, version, getContextIdentifier());
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { getContextOutput() };
        }

        public BuildObject getContextOutput()
        {
            if (outputObj == null)
            {
                outputObj = new VirtualBuildObject(
                    Path.Combine(BuildEngine.theEngine.getVirtualRoot(), Util.mungeClean(getAbstractIdentifier().ToString())+CONTEXT_EXTN));
            }
            return outputObj;
        }
    }

    static class ContextGeneratingVerbExtensions
    {
        internal static IIncludePathContext fetchIfAvailable(this IContextGeneratingVerb verb, ref DependencyDisposition ddisp)
        {
            try
            {
                return ((ContextContents)
                    BuildEngine.theEngine.getNuObjContents().openVirtual(verb.getContextOutput())).context;

            }
            catch (ObjNotReadyException)
            {
                //- oh, we don't even have the context object yet.
                ddisp = ddisp.combine(DependencyDisposition.Incomplete);
            }
            catch (ObjFailedException)
            {
                ddisp = ddisp.combine(DependencyDisposition.Failed);
            }
            return null;
        }
    }

}

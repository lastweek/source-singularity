using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    abstract class TransitiveDepsVerb
        : Verb
    {
        public const string TDEP_EXTN = ".tdep";
        const int version = 3;

        BuildObject obj;
        BuildObject _depsObj;

        protected abstract TransitiveDepsVerb factory(BuildObject obj);
        protected abstract IIncludeFactory getIncludeFactory();

        protected TransitiveDepsVerb(BuildObject obj)
        {
            this.obj = obj;
            this._depsObj = obj.makeVirtualObject(BeatExtensions.whichPart(obj).ExtnStr()+TDEP_EXTN);
        }

        public BuildObject depsObj()
        {
            return _depsObj;
        }

        public override AbstractId getAbstractIdentifier()
        {
            return new AbstractId(this.GetType().Name, version, obj.getRelativePath());
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { depsObj() };
        }

        public override IVerbWorker getWorker()
        {
            OrderPreservingSet<BuildObject> shallowDeps = new OrderPreservingSet<BuildObject>();
            OrderPreservingSet<BuildObject> transitiveDeps = new OrderPreservingSet<BuildObject>();

            IEnumerable<BuildObject> includes = getIncludeFactory().getIncludes(obj);
            foreach (BuildObject child in includes)
            {
                shallowDeps.Add(child);
                transitiveDeps.AddRange(factory(child).getTransitiveIncludes());
                transitiveDeps.Add(child);
            }
            VirtualContents contents = new TransitiveDepsContents(shallowDeps, transitiveDeps);
            BuildEngine.theEngine.getNuObjContents().storeVirtual(depsObj(), new Fresh(), contents);
            return new VerbSyncWorker(new Fresh());
        }

        //- Available only after this verb is Fresh.
        //- These are called the "transitive includes" because from this point of view, these aren't
        //- dependencies, they're the included files. The caller may be using them to describe
        //- his dependencies, though.
        public IEnumerable<BuildObject> getTransitiveIncludes()
        {
            TransitiveDepsContents contents =
                (TransitiveDepsContents)BuildEngine.theEngine.getNuObjContents().openVirtual(depsObj());
            return contents.transitiveDeps;
        }

        public IEnumerable<BuildObject> getShallowIncludes()
        {
            TransitiveDepsContents contents =
                (TransitiveDepsContents)BuildEngine.theEngine.getNuObjContents().openVirtual(depsObj());
            return contents.shallowDeps;
        }

        //- This is a helper method for the downstream verb's getDependencies().
        //- It emits this verb's output token so that if this verb is
        //- not yeat Fresh, the scheduler will strive to get this verb Executed,
        //- plus if this verb is Fresh, tacks on all of the deps computed by
        //- this verb.
        //- The returned HashSet belongs to the caller, who is free
        //- to stuff more into it.
        public HashSet<BuildObject> getAvailableDeps(out DependencyDisposition ddisp)
        {
            HashSet<BuildObject> result = new HashSet<BuildObject>();
            result.Add(depsObj());

            try
            {
                result.UnionWith(getTransitiveIncludes());
                result.Add(obj);    //- Add this last, since BoogieAsmLinkVerb appears to depend on this ordering
                ddisp = DependencyDisposition.Complete;
            }
            catch (ObjNotReadyException)
            {
                ddisp = DependencyDisposition.Incomplete;
            }
            catch (ObjFailedException)
            {
                ddisp = DependencyDisposition.Failed;
            }
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            try
            {
                IEnumerable<BuildObject> includes = getIncludeFactory().getIncludes(obj);
                //- NB evaluating eagerly so we can catch the exception here rather
                //- than hide it in a lazy evaluation later.
                List<IVerb> result = new List<IVerb>(includes.Select(parent => factory(parent)));
                return result;
            }
            catch (ObjNotReadyException)
            {
            }
            return new IVerb[] { };
        }

        protected virtual void extendDeps(List<BuildObject> deps)
        {
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            //- NB we'll either return the singleton list {obj} if obj isn't yet available,
            //- or we'll return the entire list of deps on obj's parents.
            List<BuildObject> deps = new List<BuildObject>();
            extendDeps(deps);
            deps.Add(obj);

            try
            {
                IEnumerable<BuildObject> includes = getIncludeFactory().getIncludes(obj);
                if (includes.Contains(obj))
                {
                    throw new SourceConfigurationError("Include loop starting at " + obj);
                }
                deps.AddRange(includes.Select(parent => factory(parent).depsObj()));
                ddisp = DependencyDisposition.Complete;
            }
            catch (ObjNotReadyException)
            {
                ddisp = DependencyDisposition.Incomplete;
            }
            catch (ObjFailedException)
            {
                ddisp = DependencyDisposition.Failed;
            }
            return deps;
        }
    }
}

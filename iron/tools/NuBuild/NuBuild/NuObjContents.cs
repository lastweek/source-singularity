using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{

    class NuObjValue
    {
        string _hash;
        Disposition _disp;   //- disposition of the verb that created this object.
        VirtualContents _virtualContents;   //- for objects not stored in the filesystem, here's the computed value.

        public string hash { get { return _hash; } }
        public Disposition disp { get { return _disp; } }
        public VirtualContents virtualContents { get { return _virtualContents; } }

        public NuObjValue(string hash, Disposition disp, VirtualContents virtualContents)
        {
            this._hash = hash;
            this._disp = disp;
            this._virtualContents = virtualContents;
        }
    }

    class ObjNotReadyException : Exception
    {
        public ObjNotReadyException(BuildObject obj)
            : base(obj.ToString())
        {
        }
    }

    class ObjFailedException : Exception
    {
        public ObjFailedException(BuildObject obj, Failed f)
            : base(obj.ToString() + ": " + f.ToString())
        {
        }
    }

    //- This class keeps track of the data we've stored into nuobj/.
    //- The invariant is that we never read data out of nuobj/ if it's
    //- not data we put there ourselves this execution (perhaps by
    //- fetching it from the cache). Data from the cache is safe,
    //- because it is tracked by concreteIdentifier. But data in
    //- nuobj/ may be stale, leading us to build the wrong thing.
    //- (A wrong thing would be correctly labeled, so it won't poison
    //- the cache, but it wouldn't be the output the user asked for.)
    class NuObjContents
    {
        Dictionary<BuildObject, NuObjValue> theCache;
        Hasher _hasher;

        public NuObjContents(Hasher hasher)
        {
            this._hasher = hasher;
            theCache = new Dictionary<BuildObject, NuObjValue>();
        }

        public void blessGeneral(BuildObject obj, Disposition disp)
        {
            if (obj is VirtualBuildObject)
            {
                if (disp is Fresh)
                {
                    //- The object is fresh, so the verb ran its Execute
                    //- method and squirted the results into theCache;
                    //- this call is from the scheduler cleaning up,
                    //- and we can ignore it.
                    Util.Assert(theCache.ContainsKey(obj));
                    Util.Assert(theCache[obj].disp is Fresh);
                }
                else
                {
                    Util.Assert(disp is Failed);
                    storeVirtual(obj, disp, null);
                }
            }
            else
            {
                bless(obj, null, disp);
            }
        }

        public void bless(BuildObject obj, string hashIfKnown, Disposition disp)
        {
            Util.Assert(obj.getRelativePath().StartsWith(BuildEngine.theEngine.getObjRoot()));
            blessInternal(obj, hashIfKnown, disp, null);
        }

        public void storeVirtual(BuildObject obj, Disposition disp, VirtualContents contents)
        {
            Util.Assert(obj is VirtualBuildObject);
            blessInternal(obj, null, disp, contents);
        }

        void blessInternal(BuildObject obj, string hashIfKnown, Disposition disp, VirtualContents contents)
        {
            Util.Assert(!theCache.ContainsKey(obj));    //- I don't think we should ever write the same file twice in one run.
            string hash = hashIfKnown;
            if (hash == null && disp is Fresh && !(obj is VirtualBuildObject))
            {
                hash = _hasher.hash(obj.getFilesystemPath());
            }
            theCache[obj] = new NuObjValue(hash, disp, contents);
        }

        /
        /
        public NuObjValue getValue(BuildObject obj)
        {
            if (theCache.ContainsKey(obj))
            {
                return theCache[obj];
            }
            else if (obj is SourcePath)
            {
                try
                {
                    blessInternal(obj, null, new Fresh(), null);
                }
                catch (IOException)
                {
                    throw new SourceConfigurationError("Cannot find source path "+obj.getRelativePath());
                }
                return theCache[obj];
            }
            else
            {
                return null;
            }
        }

        NuObjValue fetchFresh(BuildObject obj)
        {
            NuObjValue value = getValue(obj);
            if (value == null)
            {
                throw new ObjNotReadyException(obj);
            }
            if (value.disp is Failed)
            {
                throw new ObjFailedException(obj, (Failed) value.disp);
            }
            Util.Assert(value.disp is Fresh); //- This isn't really a 'not ready' condition; we shouldn't be here.
            return value;
        }

        public TextReader openRead(BuildObject obj)
        {
            fetchFresh(obj);
            return new StreamReader(obj.getFilesystemPath());
        }

        public VirtualContents openVirtual(BuildObject obj)
        {
            return fetchFresh(obj).virtualContents;
        }

        public Disposition getDisposition(BuildObject obj)
        {
            NuObjValue value = getValue(obj);
            if (value != null)
            {
                return value.disp;
            }
            return new Stale();
        }

        internal int dbgCacheSize()
        {
            return theCache.Count();
        }
    }
}

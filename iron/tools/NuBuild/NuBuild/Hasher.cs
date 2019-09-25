using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;

namespace NuBuild
{
    class Hasher : IHasher
    {
        Dictionary<BuildObject, IVerb> outputToVerbMap;

        private CachedHash<Tuple<IIncludePathContext,string,ModPart>, BuildObject> _contextResolutionCache;

        CachedHash<Tuple<IIncludePathContext, BuildObject>, List<BeatIncludes.LabeledInclude>> _parsedIncludesCache;

        private CachedHash<string, string> _marshalledFilesystemPaths = new CachedHash<string, string>(delegate(string filesystemPath)
        {
            return Util.hashFilesystemPath(filesystemPath);
        });

        public Hasher()
        {
            outputToVerbMap = new Dictionary<BuildObject, IVerb>();

            _contextResolutionCache = new CachedHash<Tuple<IIncludePathContext, string, ModPart>, BuildObject>(
                delegate(Tuple<IIncludePathContext, string, ModPart> key) {
                    return key.Item1.search(key.Item2, key.Item3);
                });

            _parsedIncludesCache = new CachedHash<Tuple<IIncludePathContext, BuildObject>, List<BeatIncludes.LabeledInclude>>(
                delegate(Tuple<IIncludePathContext, BuildObject> key)
                {
                    return BeatIncludes.parseLabeledIncludes(key.Item1, key.Item2);
                });
        }

        public string hash(string filesystemPath)
        {
            return _marshalledFilesystemPaths.get(filesystemPath);
        }
        public BuildObject search(IIncludePathContext context, string modName, ModPart modPart)
        {
            return _contextResolutionCache.get(new Tuple<IIncludePathContext, string, ModPart>(context, modName, modPart));
        }

        public IVerb getParent(BuildObject dep)
        {
            IVerb result;
            outputToVerbMap.TryGetValue(dep, out result);
            return result;
        }

        void IHasher.addVerb(IVerb verb)
        {
            foreach (BuildObject obj in verb.getOutputs())
            {
                if (outputToVerbMap.ContainsKey(obj))
                {
                    Util.Assert(outputToVerbMap[obj].Equals(verb));
                }
                else
                {
                    outputToVerbMap[obj] = verb;
                }
            }
        }

        public List<BeatIncludes.LabeledInclude> getParsedIncludes(IIncludePathContext context, BuildObject beatsrc)
        {
            return _parsedIncludesCache.get(new Tuple<IIncludePathContext, BuildObject>(context, beatsrc));
        }
    }
}

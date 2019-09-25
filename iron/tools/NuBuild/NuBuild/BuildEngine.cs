using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class BuildEngine
    {
        private static BuildEngine _theEngine = new BuildEngine();

        public static BuildEngine theEngine { get { return _theEngine; } }

        PathNormalizer pathNormalizer;
        SourcePathIncludeContext vervePathContext;
        string ironRoot;
        Hasher _hasher;
        NuObjContents nuObjContents;
        string localCacheLocation = "nucache";

        BuildEngine()
        {
            pathNormalizer = new PathNormalizer();
            _hasher = new Hasher();
            nuObjContents = new NuObjContents(_hasher);
        }

        public const string VerveTrustedSpecDir = "Trusted\\Spec";

        public SourcePathIncludeContext getVervePathContext()
        {
            if (vervePathContext == null)
            {
                Util.Assert(ironRoot != null);
                vervePathContext = new SourcePathIncludeContext();
                vervePathContext.addDirectory(VerveTrustedSpecDir);
                vervePathContext.addDirectory("Checked/Nucleus/Base");
                vervePathContext.addDirectory("Checked/Nucleus/GC");
                vervePathContext.addDirectory("Checked/Nucleus/Devices");
                vervePathContext.addDirectory("Checked/Nucleus/Main");

                vervePathContext.addDstExtension(BeatExtensions.BEATIFC_EXTN);
                vervePathContext.addDstExtension(BeatExtensions.BEATIMP_EXTN);
                vervePathContext.addDstExtension(BoogieAsmVerifyVerb.BASMIFC_EXTN);
                vervePathContext.addDstExtension(BoogieAsmVerifyVerb.BASMIMP_EXTN);
            }
            return vervePathContext;
        }

        public IContextGeneratingVerb getVerveContextVerb(PoundDefines poundDefines)
        {
            return new StaticContextVerb(getVervePathContext(), "Verve", poundDefines);
        }

        //-public TransitiveIncludesCache getDafnyIncludeCache()
        //-{
        //-    return dafnyIncludeCache;
        //-}

        //-public TransitiveIncludesCache getBeatIncludeCache(IIncludePathContext context)
        //-{
        //-    if (!contextToCache.ContainsKey(context))
        //-    {
        //-        contextToCache[context] = new TransitiveIncludesCache(new BeatIncludes(context));
        //-    }
        //-    return contextToCache[context];
        //-}

        public string getIronRoot()
        {
            return ironRoot;
        }

        internal void setIronRoot(string ironRoot)
        {
            this.ironRoot = pathNormalizer.normalizeAbsolutePath(ironRoot);
        }

        //- Normalize the case of an ironRoot-relative path to the case present in the filesystem
        internal string normalizeIronPath(string ironRelPath)
        {
            string abspath = pathNormalizer.normalizeAbsolutePath(Path.GetFullPath(Path.Combine(ironRoot, ironRelPath)));
            Util.Assert(abspath.StartsWith(ironRoot));
            return abspath.Substring(ironRoot.Length);
        }

        internal string getObjRoot() { return "nuobj"; }
        internal string getSrcRoot() { return "src"; }
        internal string getVirtualRoot() { return getObjRoot()+"\\virtual"; }  //- should never exist in filesystem!
        internal string getToolsRoot() { return "tools"; }
        internal string getBinToolsRoot() { return "bin_tools"; }

        internal void setLocalCache(string path)
        {
            localCacheLocation = path;
        }
        internal string getLocalCache()
        {
            return localCacheLocation;
        }

        internal NuObjContents getNuObjContents()
        {
            return nuObjContents;
        }

        internal IHasher getHasher()
        {
            return _hasher;
        }
    }
}

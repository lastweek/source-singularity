using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Text.RegularExpressions;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class BeatIncludes
    {
        public enum ImportFilter { ForBeatOrBasm, ForBasmOnly };

        class FetchModuleCache
        {
            CachedHash<string, BuildObject> cache;
            BeatIncludes beatIncludes;
            public FetchModuleCache(IIncludePathContext context)
            {
                this.beatIncludes = new BeatIncludes(context);
                this.cache = new CachedHash<string, BuildObject>(fetchModule);
            }
            private BuildObject fetchModule(string module) { return beatIncludes.fetchModule(module); }
            public BuildObject get(string module) { return cache.get(module); }
        }

        static CachedHash<IIncludePathContext, FetchModuleCache> fetchModuleCaches
            = new CachedHash<IIncludePathContext, FetchModuleCache>(delegate(IIncludePathContext context)
                {
                    return new FetchModuleCache(context); });
        
        IIncludePathContext includePathSearcher;

        public BeatIncludes(IIncludePathContext includePathSearcher)
        {
            this.includePathSearcher = includePathSearcher;
        }

        public class LabeledInclude
        {
            public ImportFilter importFilter;
            public BuildObject buildObject;
            public LabeledInclude(ImportFilter importFilter, BuildObject buildObject)
            {
                this.importFilter = importFilter;
                this.buildObject = buildObject;
            }
        }

        public List<LabeledInclude> getLabeledIncludes(BuildObject beatsrc)
        {
            //-return caches.get(includePathSearcher).get(beatsrc);
            return computeLabeledIncludes(beatsrc);
        }

        protected List<LabeledInclude> computeLabeledIncludes(BuildObject beatsrc)
        {
            return BuildEngine.theEngine.getHasher().getParsedIncludes(includePathSearcher, beatsrc);
        }
        public static List<LabeledInclude> parseLabeledIncludes(IIncludePathContext context, BuildObject beatsrc)
        {
            //-Logger.WriteLine("parseLabeledIncludes " + beatsrc.getRelativePath() + " context " + context.GetHashCode());

            List<LabeledInclude> outlist = new List<LabeledInclude>();
            //-Regex re = new Regex("^\\s*import\\s*([^\\s,]*(,\\s*[^\\s,]*)*)\\s*;");
            //- TODO allow commented-out imports until Beat accepts (ignores) them in ifcs files.
            Regex import_re = new Regex("^[\\s/-]*private-import\\s*([^\\s,]*(,\\s*[^\\s,]*)*)\\s*;");
            Regex basmonly_re = new Regex("^[\\s/-]*private-basmonly-import\\s*([^\\s,]*(,\\s*[^\\s,]*)*)\\s*;");
            FetchModuleCache fmcache = fetchModuleCaches.get(context);
            using (TextReader tr = BuildEngine.theEngine.getNuObjContents().openRead(beatsrc))
            {
                while (true)
                {
                    string line = tr.ReadLine();
                    if (line == null)
                    {
                        break;
                    }
                    Match match = import_re.Match(line);
                    if (match.Success)
                    {
                        outlist.Add(new LabeledInclude(ImportFilter.ForBeatOrBasm, fmcache.get(match.Groups[1].ToString())));
                    }
                    match = basmonly_re.Match(line);
                    if (match.Success)
                    {
                        outlist.Add(new LabeledInclude(ImportFilter.ForBasmOnly, fmcache.get(match.Groups[1].ToString())));

                    }
                }
                //-Logger.WriteLine(String.Format("{0} includes {1} things", dfysource.getFilesystemPath(), outlist.Count));
                return outlist;
            }
        }

        public IEnumerable<BuildObject> getBasmIncludes(BuildObject beatsrc)
        {
            return computeLabeledIncludes(beatsrc).Select(li => li.buildObject);
        }

        private BuildObject fetchModule(string module)
        {
            //-Logger.WriteLine("fetchmodule " + module + " ctx " + includePathSearcher.GetHashCode());
            string includedModule = module.Trim();
            BuildObject path = includePathSearcher.search(includedModule);
            if (path == null)
            {
                throw new SourceConfigurationError(
                    String.Format("Cannot find module {0} in search path {1}",
                    includedModule, includePathSearcher));
            }
            return path;
        }
    }
}

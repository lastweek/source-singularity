using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class BasmObligationIncludes
        : IIncludeFactory
    {
        IIncludePathContext includePathSearcher;
        BeatIncludes directIncludes;

        public BasmObligationIncludes(IIncludePathContext includePathSearcher)
        {
            this.includePathSearcher = includePathSearcher;
            this.directIncludes = new BeatIncludes(includePathSearcher);
        }

        public IEnumerable<BuildObject> getIncludes(BuildObject beatsrc)
        {
            IHasher hasher = BuildEngine.theEngine.getHasher();
            OrderPreservingSet<BuildObject> includes = new OrderPreservingSet<BuildObject>();

            //-BuildObject ifcFile = includePathSearcher.search(beatsrc.getFileNameWithoutExtension(), ModPart.Ifc);
            //-BuildObject impFile = includePathSearcher.search(beatsrc.getFileNameWithoutExtension(), ModPart.Imp);
            BuildObject ifcFile = hasher.search(includePathSearcher, beatsrc.getFileNameWithoutExtension(), ModPart.Ifc);
            BuildObject impFile = hasher.search(includePathSearcher, beatsrc.getFileNameWithoutExtension(), ModPart.Imp);
            
            Util.Assert(ifcFile.Equals(beatsrc) || impFile.Equals(beatsrc));
            includes.AddRange(directIncludes.getBasmIncludes(ifcFile));
            includes.AddRange(directIncludes.getBasmIncludes(impFile));
            return includes;
        }
    }
}

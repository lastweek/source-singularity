using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    interface IHasher
    {
        string hash(string filesystemPath);
        BuildObject search(IIncludePathContext context, string modName, ModPart modPart);
        IVerb getParent(BuildObject dep);
        void addVerb(IVerb verb);

        List<BeatIncludes.LabeledInclude> getParsedIncludes(IIncludePathContext context, BuildObject beatsrc);
    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    //- A VirtualBuildObject is never actually stored in the filesystem;
    //- it is only materialized inside the process. It's used for results
    //- that are easy to compute, but which still need to be established
    //- in dependency order. Instances: transitive deps, contexts.
    class VirtualBuildObject
        : BuildObject
    {
        public VirtualBuildObject(string inpath)
            : base(inpath)
        {
            Util.Assert(inpath.StartsWith(BuildEngine.theEngine.getVirtualRoot()));
        }

        public override void prepareObjDirectory()
        {
            //- virtual objects don't go to the filesystem
        }

        public override string getFilesystemPath()
        {
            Util.Assert(false);
            return null;
			//- Caller: you definitely don't want to put this virtual object into the FS.
        }

    }
}

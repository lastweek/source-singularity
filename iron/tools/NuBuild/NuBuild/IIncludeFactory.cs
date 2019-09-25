using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    interface IIncludeFactory
    {
        IEnumerable<BuildObject> getIncludes(BuildObject path);
    }
}

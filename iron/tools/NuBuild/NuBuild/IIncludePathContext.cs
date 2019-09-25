using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    interface IIncludePathContext
    {
        BuildObject search(string basename, ModPart modPart = ModPart.Ifc);
    }
}

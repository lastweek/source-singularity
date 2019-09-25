using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    abstract class IncludePathContext
        : IIncludePathContext
    {
        public abstract BuildObject search(string basename, ModPart modPart = ModPart.Ifc);

        public override int GetHashCode()
        {
            return ToString().GetHashCode();
        }

        public override bool Equals(object obj)
        {
            return ToString().Equals(obj.ToString());
        }
    }
}

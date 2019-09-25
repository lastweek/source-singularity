using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    interface IKnownObjectHash
    {
        //- returns null if obj isn't available ... or even if it is, but wasn't written during this run,
        //- so we're not sure it's the input we want to compute over.
        string getKnownObjectHash(BuildObject obj);
    }
}

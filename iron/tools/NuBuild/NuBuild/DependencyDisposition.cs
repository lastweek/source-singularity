using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    public enum DependencyDisposition
    {
        Complete,
        Incomplete,
        Failed      //- Something failed upstream
    }

    public static class DependencyDispositionExtensions
    {
        public static DependencyDisposition combine(this DependencyDisposition a, DependencyDisposition b)
        {
            if (a == DependencyDisposition.Failed || b == DependencyDisposition.Failed)
            {
                return DependencyDisposition.Failed;
            }
            if (a == DependencyDisposition.Incomplete || b == DependencyDisposition.Incomplete)
            {
                return DependencyDisposition.Incomplete;
            }
            return DependencyDisposition.Complete;
        }
    }
}

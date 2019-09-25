using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class ContextContents
        : VirtualContents
    {
        IIncludePathContext _context;
        public IIncludePathContext context { get { return _context; } }

        public ContextContents(IIncludePathContext context)
        {
            this._context = context;
        }

    }
}

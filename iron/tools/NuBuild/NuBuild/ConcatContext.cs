using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class ConcatContext
        : IncludePathContext
    {
        List<IIncludePathContext> _contexts;
        string _descr;
        
        public ConcatContext(IEnumerable<IIncludePathContext> contexts)
        {
            _contexts = new List<IIncludePathContext>(contexts);
            _descr = "Context(" + String.Join(",", _contexts) + ")";
        }

        public override string ToString()
        {
            return _descr;
        }

        public override BuildObject search(string basename, ModPart modPart = ModPart.Ifc)
        {
            foreach (IIncludePathContext context in _contexts)
            {
                BuildObject obj = context.search(basename, modPart);
                if (obj != null)
                {
                    return obj;
                }
            }
            return null;
        }
    }
}

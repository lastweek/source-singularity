using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class UserError : Exception
    {
        public UserError(string msg)
            : base(msg)
        { }
    }
}

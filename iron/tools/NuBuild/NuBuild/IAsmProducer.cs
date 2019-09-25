using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    interface IAsmProducer : IVerb
    {
        BuildObject getAsmFile();
    }
}

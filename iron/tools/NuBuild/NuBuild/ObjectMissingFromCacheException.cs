using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class ObjectMissingFromCacheException
        : Exception
    {
        string itemHash;

        public ObjectMissingFromCacheException(string itemHash, string msg)
            : base(String.Format("item {0} missing from cache: {1}", itemHash, msg))
        {
            this.itemHash = itemHash;
        }
    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;

namespace NuBuild
{
    class CachedHash<HashedObjectType,ValueType>
    {
        public enum FailureBehavior { IgnoreFailures, AssertFailures };
        public delegate ValueType HashFunc(HashedObjectType hashObj);
        public delegate bool CachabilityTestFunc(ValueType value);

        private Dictionary<HashedObjectType, ValueType> _hashCache;
        private HashFunc _hashFunc;
        private FailureBehavior _failureBehavior;
        private CachabilityTestFunc _cachabilityTest;

        public CachedHash(HashFunc hashFunc,
            FailureBehavior failureBehavior = FailureBehavior.AssertFailures,
            CachabilityTestFunc cachabilityTest = null)
        {
            this._hashCache = new Dictionary<HashedObjectType, ValueType>();
            this._hashFunc = hashFunc;
            this._failureBehavior = failureBehavior;
            this._cachabilityTest = cachabilityTest;
        }

        public ValueType get(HashedObjectType hashObj)
        {
            if (!_hashCache.ContainsKey(hashObj)) {
                ValueType value = _hashFunc(hashObj);
                if (value == null)
                {
                    Util.Assert(_failureBehavior == FailureBehavior.IgnoreFailures);
                    return value;
                }
                else if (_cachabilityTest != null && !_cachabilityTest(value))
                {
                    return value;
                }
                else
                {
                    _hashCache[hashObj] = value;
                }
            }

            return _hashCache[hashObj];
        }
    }
}

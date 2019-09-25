using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    //- inspired by ICollection example at
    //- http://stackoverflow.com/questions/1552225/hashset-that-preserves-ordering
    class OrderPreservingSet<T>
        : ICollection<T>
    {
        private readonly HashSet<T> membership;
        private readonly List<T> order;

        public OrderPreservingSet()
            : this(EqualityComparer<T>.Default)
        {
        }

        public OrderPreservingSet(IEqualityComparer<T> comparer)
        {
            membership = new HashSet<T>(comparer);
            order = new List<T>();
        }

        public OrderPreservingSet(IEnumerable<T> initialContents)
            : this()
        {
            AddRange(initialContents);
        }

        public int Count { get { return membership.Count(); } }

        public void AddRange(IEnumerable<T> range)
        {
            foreach (T obj in range)
            {
                Add(obj);
            }
        }

        public void Add(T item)
        {
            if (!membership.Contains(item))
            {
                membership.Add(item);
                order.Add(item);
            }
        }

        void ICollection<T>.Add(T item)
        {
            Add(item);
        }

        void ICollection<T>.Clear()
        {
            membership.Clear();
            order.Clear();
        }

        bool ICollection<T>.Contains(T item)
        {
            return membership.Contains(item);
        }

        void ICollection<T>.CopyTo(T[] array, int arrayIndex)
        {
            order.CopyTo(array, arrayIndex);
        }

        int ICollection<T>.Count
        {
            get { return membership.Count; }
        }

        
        bool ICollection<T>.IsReadOnly
        {
            get { return false; }
        }

        bool ICollection<T>.Remove(T item)
        {
            membership.Remove(item);
            return order.Remove(item);
        }

        IEnumerator<T> IEnumerable<T>.GetEnumerator()
        {
            return order.GetEnumerator();
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
        {
            return order.GetEnumerator();
        }
    }
}

// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Text;

namespace Microsoft.Singularity.Applications
{
    class HashSet : ISet
    {
        Hashtable table;
        ArrayList list;
        public HashSet()
        {
            table = new Hashtable();
            list = new ArrayList();
        }

        public HashSet(ICollection i)
            : this()
        {
            AddAll(i);
        }
        public bool Contains(Object elem)
        {
            return table.ContainsKey(elem);
        }

        public void Add(Object elem)
        {
            if (Contains(elem)) return;
            int index = list.Add(elem);
            table[elem] = index;
        }

        public void AddAll(ICollection coll)
        {
            if (coll == null) return;
            foreach (Object obj in coll) {
                Add(obj);
            }
        }

        public void Remove(Object obj)
        {
            Object index = table[obj];
            if (index == null) return;
            list.RemoveAt((int)index);
            table.Remove(obj);
        }
        public int Count
        {
            get
            {
                return table.Count;
            }
        }

        public void CopyTo(System.Array arr, int n)
        {
            int i = n;
            foreach (Object key in table.Keys) {
                arr.SetValue(key, n++);
            }
        }

        public Object SyncRoot
        {
            get { throw new InvalidOperationException("operation not supported"); }
        }

        public bool IsSynchronized
        {
            get { return false; }
        }

        public override bool Equals(object obj)
        {
            if (!(obj is ISet)) return false;
            return this.ContainsAll(((ISet)obj)) && ((ISet)obj).ContainsAll(this); ; //sort maybe?
        }

        public bool ContainsAll(ISet thatCol)
        {
            foreach (DictionaryEntry entry in table) {
                Object key = entry.Key;
                ISet that = thatCol as ISet;
                if (!that.Contains(key)) return false;
            }
            return true;
        }

        public IEnumerator GetEnumerator()
        {
            return list.GetEnumerator();
        }

        public override int GetHashCode()
        {
            int hash = 0;
            foreach (DictionaryEntry entry in table) {
                hash ^= entry.Key.GetHashCode();
            }

            return hash;
        }

        public override string ToString()
        {
            StringBuilder sb = new StringBuilder();
            bool first = true;
            foreach (Object elem in table.Keys) {
                sb.Append(elem.ToString() + (first ? "" : " , "));
            }
            return sb.ToString();
        }
    }
}

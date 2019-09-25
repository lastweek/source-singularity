// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

namespace System.Collections
{
    using System;

    // Useful base class for typed read/write collections where items derive from object
    //| <include path='docs/doc[@for="CollectionBase"]/*' />
    public abstract class CollectionBase : IList {
        ArrayList list;

        //| <include path='docs/doc[@for="CollectionBase.InnerList"]/*' />
        protected ArrayList InnerList {
            get {
                if (list == null)
                    list = new ArrayList();
                return list;
            }
        }

        //| <include path='docs/doc[@for="CollectionBase.List"]/*' />
        protected IList List {
            get { return (IList)this; }
        }

        //| <include path='docs/doc[@for="CollectionBase.Count"]/*' />
        public int Count {
            get {
                return list == null ? 0 : list.Count;
            }
        }

        //| <include path='docs/doc[@for="CollectionBase.Clear"]/*' />
        public void Clear() {
            OnClear();
            InnerList.Clear();
            OnClearComplete();
        }

        //| <include path='docs/doc[@for="CollectionBase.RemoveAt"]/*' />
        public void RemoveAt(int index) {
            if (index < 0 || index >= InnerList.Count)
                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_Index");
            Object temp = InnerList[index];
            OnValidate(temp);
            OnRemove(index, temp);
            InnerList.RemoveAt(index);
            OnRemoveComplete(index, temp);
        }

        //| <include path='docs/doc[@for="CollectionBase.IList.IsReadOnly"]/*' />
        bool IList.IsReadOnly {
            get { return InnerList.IsReadOnly; }
        }

        //| <include path='docs/doc[@for="CollectionBase.IList.IsFixedSize"]/*' />
        bool IList.IsFixedSize {
            get { return InnerList.IsFixedSize; }
        }

        //| <include path='docs/doc[@for="CollectionBase.ICollection.IsSynchronized"]/*' />
        bool ICollection.IsSynchronized {
            get { return InnerList.IsSynchronized; }
        }

        //| <include path='docs/doc[@for="CollectionBase.ICollection.SyncRoot"]/*' />
        Object ICollection.SyncRoot {
            get { return InnerList.SyncRoot; }
        }

        //| <include path='docs/doc[@for="CollectionBase.ICollection.CopyTo"]/*' />
        void ICollection.CopyTo(Object[] array, int index) {
            InnerList.CopyTo(array, index);
        }

        //| <include path='docs/doc[@for="CollectionBase.IList.this"]/*' />
        Object IList.this[int index] {
            get {
                if (index < 0 || index >= InnerList.Count)
                    throw new ArgumentOutOfRangeException("ArgumentOutOfRange_Index");
                return InnerList[index];
            }
            set {
                if (index < 0 || index >= InnerList.Count)
                    throw new ArgumentOutOfRangeException("ArgumentOutOfRange_Index");
                OnValidate(value);
                Object temp = InnerList[index];
                OnSet(index, temp, value);
                InnerList[index] = value;
                try {
                    OnSetComplete(index, temp, value);
                }
                catch (Exception) {
                    InnerList[index] = temp;
                    throw;
                }
            }
        }

        //| <include path='docs/doc[@for="CollectionBase.IList.Contains"]/*' />
        bool IList.Contains(Object value) {
            return InnerList.Contains(value);
        }

        //| <include path='docs/doc[@for="CollectionBase.IList.Add"]/*' />
        int IList.Add(Object value) {
            OnValidate(value);
            OnInsert(InnerList.Count, value);
            int index = InnerList.Add(value);
            try {
                OnInsertComplete(index, value);
            }
            catch (Exception) {
                InnerList.RemoveAt(index);
                throw;
            }
            return index;
        }


        //| <include path='docs/doc[@for="CollectionBase.IList.Remove"]/*' />
        void IList.Remove(Object value) {
            OnValidate(value);
            int index = InnerList.IndexOf(value);
            if (index < 0) throw new ArgumentException("Arg_RemoveArgNotFound");
            OnRemove(index, value);
            InnerList.RemoveAt(index);
            OnRemoveComplete(index, value);
        }

        //| <include path='docs/doc[@for="CollectionBase.IList.IndexOf"]/*' />
        int IList.IndexOf(Object value) {
            return InnerList.IndexOf(value);
        }

        //| <include path='docs/doc[@for="CollectionBase.IList.Insert"]/*' />
        void IList.Insert(int index, Object value) {
            if (index < 0 || index > InnerList.Count)
                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_Index");
            OnValidate(value);
            OnInsert(index, value);
            InnerList.Insert(index, value);
            try {
                OnInsertComplete(index, value);
            }
            catch (Exception) {
                InnerList.RemoveAt(index);
                throw;
            }
        }

        //| <include path='docs/doc[@for="CollectionBase.GetEnumerator"]/*' />
        public IEnumerator GetEnumerator() {
            return InnerList.GetEnumerator();
        }

        //| <include path='docs/doc[@for="CollectionBase.OnSet"]/*' />
        protected virtual void OnSet(int index, Object oldValue, Object newValue) {
        }

        //| <include path='docs/doc[@for="CollectionBase.OnInsert"]/*' />
        protected virtual void OnInsert(int index, Object value) {
        }

        //| <include path='docs/doc[@for="CollectionBase.OnClear"]/*' />
        protected virtual void OnClear() {
        }

        //| <include path='docs/doc[@for="CollectionBase.OnRemove"]/*' />
        protected virtual void OnRemove(int index, Object value) {
        }

        //| <include path='docs/doc[@for="CollectionBase.OnValidate"]/*' />
        protected virtual void OnValidate(Object value) {
            if (value == null) throw new ArgumentNullException("value");
        }

        //| <include path='docs/doc[@for="CollectionBase.OnSetComplete"]/*' />
        protected virtual void OnSetComplete(int index, Object oldValue, Object newValue) {
        }

        //| <include path='docs/doc[@for="CollectionBase.OnInsertComplete"]/*' />
        protected virtual void OnInsertComplete(int index, Object value) {
        }

        //| <include path='docs/doc[@for="CollectionBase.OnClearComplete"]/*' />
        protected virtual void OnClearComplete() {
        }

        //| <include path='docs/doc[@for="CollectionBase.OnRemoveComplete"]/*' />
        protected virtual void OnRemoveComplete(int index, Object value) {
        }

    }

}

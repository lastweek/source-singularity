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
    //| <include path='docs/doc[@for="DictionaryBase"]/*' />
    public abstract class DictionaryBase : IDictionary {
        Hashtable hashtable;

        //| <include path='docs/doc[@for="DictionaryBase.InnerHashtable"]/*' />
        protected Hashtable InnerHashtable {
            get {
                if (hashtable == null)
                    hashtable = new Hashtable();
                return hashtable;
            }
        }

        //| <include path='docs/doc[@for="DictionaryBase.Dictionary"]/*' />
        protected IDictionary Dictionary {
            get { return (IDictionary) this; }
        }

        //| <include path='docs/doc[@for="DictionaryBase.Count"]/*' />
        public int Count {
            // to avoid newing inner list if no items are ever added
            get { return hashtable == null ? 0 : hashtable.Count; }
        }

        //| <include path='docs/doc[@for="DictionaryBase.IDictionary.IsReadOnly"]/*' />
        bool IDictionary.IsReadOnly {
            get { return InnerHashtable.IsReadOnly; }
        }

        //| <include path='docs/doc[@for="DictionaryBase.IDictionary.IsFixedSize"]/*' />
        bool IDictionary.IsFixedSize {
            get { return InnerHashtable.IsFixedSize; }
        }

        //| <include path='docs/doc[@for="DictionaryBase.ICollection.IsSynchronized"]/*' />
        bool ICollection.IsSynchronized {
            get { return InnerHashtable.IsSynchronized; }
        }

        //| <include path='docs/doc[@for="DictionaryBase.IDictionary.Keys"]/*' />
        ICollection IDictionary.Keys {
            get {
                return InnerHashtable.Keys;
            }
        }

        //| <include path='docs/doc[@for="DictionaryBase.ICollection.SyncRoot"]/*' />
        Object ICollection.SyncRoot {
            get { return InnerHashtable.SyncRoot; }
        }

        //| <include path='docs/doc[@for="DictionaryBase.IDictionary.Values"]/*' />
        ICollection IDictionary.Values {
            get {
                return InnerHashtable.Values;
            }
        }

        //| <include path='docs/doc[@for="DictionaryBase.CopyTo"]/*' />
        public void CopyTo(Object[] array, int index) {
            InnerHashtable.CopyTo(array, index);
        }

        //| <include path='docs/doc[@for="DictionaryBase.IDictionary.this"]/*' />
        object IDictionary.this[object key] {
            get {
                OnGet(key, InnerHashtable[key]);
                return InnerHashtable[key];
            }
            set {
                OnValidate(key, value);
                Object temp = InnerHashtable[key];
                OnSet(key, temp, value);
                InnerHashtable[key] = value;
                try {
                    OnSetComplete(key, temp, value);
                }
                catch (Exception) {
                   InnerHashtable[key] = temp;
                   throw;
                }
            }
        }

        //| <include path='docs/doc[@for="DictionaryBase.IDictionary.Contains"]/*' />
        bool IDictionary.Contains(object key) {
            return InnerHashtable.Contains(key);
        }

        //| <include path='docs/doc[@for="DictionaryBase.IDictionary.Add"]/*' />
        void IDictionary.Add(object key, object value) {
            OnValidate(key, value);
            OnInsert(key, value);
            InnerHashtable.Add(key, value);
            try {
                OnInsertComplete(key, value);
            }
            catch (Exception) {
                InnerHashtable.Remove(key);
                throw;
            }
        }

        //| <include path='docs/doc[@for="DictionaryBase.Clear"]/*' />
        public void Clear() {
            OnClear();
            InnerHashtable.Clear();
            OnClearComplete();
        }

        //| <include path='docs/doc[@for="DictionaryBase.IDictionary.Remove"]/*' />
        void IDictionary.Remove(object key) {
            Object temp = InnerHashtable[key];
            OnValidate(key, temp);
            OnRemove(key, temp);
            InnerHashtable.Remove(key);
            OnRemoveComplete(key, temp);
        }

        //| <include path='docs/doc[@for="DictionaryBase.GetEnumerator"]/*' />
        public IDictionaryEnumerator GetEnumerator() {
            return InnerHashtable.GetEnumerator();
        }

        //| <include path='docs/doc[@for="DictionaryBase.IEnumerable.GetEnumerator"]/*' />
        IEnumerator IEnumerable.GetEnumerator() {
            return InnerHashtable.GetEnumerator();
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnGet"]/*' />
        protected virtual object OnGet(object key, object currentValue) {
            return currentValue;
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnSet"]/*' />
        protected virtual void OnSet(object key, object oldValue, object newValue) {
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnInsert"]/*' />
        protected virtual void OnInsert(object key, object value) {
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnClear"]/*' />
        protected virtual void OnClear() {
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnRemove"]/*' />
        protected virtual void OnRemove(object key, object value) {
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnValidate"]/*' />
        protected virtual void OnValidate(object key, object value) {
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnSetComplete"]/*' />
        protected virtual void OnSetComplete(object key, object oldValue, object newValue) {
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnInsertComplete"]/*' />
        protected virtual void OnInsertComplete(object key, object value) {
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnClearComplete"]/*' />
        protected virtual void OnClearComplete() {
        }

        //| <include path='docs/doc[@for="DictionaryBase.OnRemoveComplete"]/*' />
        protected virtual void OnRemoveComplete(object key, object value) {
        }

    }

}

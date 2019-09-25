//------------------------------------------------------------------------------
// <copyright file="ListDictionary.cs" company="Microsoft">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//------------------------------------------------------------------------------

namespace System.Collections.Specialized
{

    using System.Collections;

    /// <devdoc>
    ///  <para>
    ///    This is a simple implementation of IDictionary using a singly linked list. This
    ///    will be smaller and faster than a Hashtable if the number of elements is 10 or less.
    ///    This should not be used if performance is important for large numbers of elements.
    ///  </para>
    /// </devdoc>
    public class ListDictionary: IDictionary {
        DictionaryNode head;
        int version;
        int count;
        IComparer comparer;

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public ListDictionary() {
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public ListDictionary(IComparer comparer) {
            this.comparer = comparer;
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public object this[object key] {
            get {
                if (key == null) {
                    throw new ArgumentNullException("key");
                }
                DictionaryNode node = head;
                if (comparer == null) {
                    while (node != null) {
                        if (key.Equals(node.key)) {
                            return node.value;
                        }
                        node = node.next;
                    }
                }
                else {
                    while (node != null) {
                        if (comparer.Compare(key, node.key) == 0) {
                            return node.value;
                        }
                        node = node.next;
                    }
                }
                return null;
            }
            set {
                if (key == null) {
                    throw new ArgumentNullException("key");
                }
                version++;
                DictionaryNode last = null;
                DictionaryNode node;
                for (node = head; node != null; node = node.next) {
                    if ((comparer == null) ? key.Equals(node.key) : comparer.Compare(key, node.key) == 0) {
                        break;
                    }
                    last = node;
                }
                if (node != null) {
                    // Found it
                    node.value = value;
                    return;
                }
                // Not found, so add a new one
                DictionaryNode newNode = new DictionaryNode();
                newNode.key = key;
                newNode.value = value;
                if (last != null) {
                    last.next = newNode;
                }
                else {
                    head = newNode;
                }
                count++;
            }
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public int Count {
            get {
                return count;
            }
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public ICollection Keys {
            get {
                return new NodeKeyValueCollection(this, true);
            }
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public bool IsReadOnly {
            get {
                return false;
            }
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public bool IsFixedSize {
            get {
                return false;
            }
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public bool IsSynchronized {
            get {
                return false;
            }
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public object SyncRoot {
            get {
                return this;
            }
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public ICollection Values {
            get {
                return new NodeKeyValueCollection(this, false);
            }
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public void Add(object key, object value) {
            if (key == null) {
                throw new ArgumentNullException("key");
            }
            version++;
            DictionaryNode last = null;
            DictionaryNode node;
            for (node = head; node != null; node = node.next) {
                if ((comparer == null) ? key.Equals(node.key) : comparer.Compare(key, node.key) == 0) {
                    throw new ArgumentException("An entry with the same key already exists.");
                }
                last = node;
            }
            // Not found, so add a new one
            DictionaryNode newNode = new DictionaryNode();
            newNode.key = key;
            newNode.value = value;
            if (last != null) {
                last.next = newNode;
            }
            else {
                head = newNode;
            }
            count++;
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public void Clear() {
            count = 0;
            head = null;
            version++;
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public bool Contains(object key) {
            if (key == null) {
                throw new ArgumentNullException("key");
            }
            for (DictionaryNode node = head; node != null; node = node.next) {
                if ((comparer == null) ? key.Equals(node.key) : comparer.Compare(key, node.key) == 0) {
                    return true;
                }
            }
            return false;
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public void CopyTo(Array array, int index)  {
            if (array == null)
                throw new ArgumentNullException("array");
            if (index < 0)
                throw new ArgumentOutOfRangeException("index");

            if (array.Length - index < count)
                throw new ArgumentException("Insufficient space");

            for (DictionaryNode node = head; node != null; node = node.next) {
                array.SetValue(new DictionaryEntry(node.key, node.value), index);
                index++;
            }
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public IDictionaryEnumerator GetEnumerator() {
            return new NodeEnumerator(this);
        }

        IEnumerator IEnumerable.GetEnumerator() {
            return new NodeEnumerator(this);
        }

        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public void Remove(object key) {
            if (key == null) {
                throw new ArgumentNullException("key");
            }
            version++;
            DictionaryNode last = null;
            DictionaryNode node;
            for (node = head; node != null; node = node.next) {
                if ((comparer == null) ? key.Equals(node.key) : comparer.Compare(key, node.key) == 0) {
                    break;
                }
                last = node;
            }
            if (node == null) {
                return;
            }
            if (node == head) {
                head = node.next;
            }
            else {
                last.next = node.next;
            }
            count--;
        }

        private class NodeEnumerator : IDictionaryEnumerator {
            ListDictionary list;
            DictionaryNode current;
            int version;
            bool start;


            public NodeEnumerator(ListDictionary list) {
                this.list = list;
                version = list.version;
                start = true;
                current = null;
            }

            public object Current {
                get {
                    return Entry;
                }
            }

            public DictionaryEntry Entry {
                get {
                    if (current == null) {
                        throw new InvalidOperationException();
                    }
                    return new DictionaryEntry(current.key, current.value);
                }
            }

            public object Key {
                get {
                    if (current == null) {
                        throw new InvalidOperationException();
                    }
                    return current.key;
                }
            }

            public object Value {
                get {
                    if (current == null) {
                        throw new InvalidOperationException();
                    }
                    return current.value;
                }
            }

            public bool MoveNext() {
                if (version != list.version) {
                    throw new InvalidOperationException("Collection was modified after the enumerator was instantiated.");
                }
                if (start) {
                    current = list.head;
                    start = false;
                }
                else if(current != null) {
                    current = current.next;
                }
                return (current != null);
            }

            public void Reset() {
                if (version != list.version) {
                    throw new InvalidOperationException("Collection was modified after the enumerator was instantiated.");
                }
                start = true;
                current = null;
            }

        }


        private class NodeKeyValueCollection : ICollection {
            ListDictionary list;
            bool isKeys;

            public NodeKeyValueCollection(ListDictionary list, bool isKeys) {
                this.list = list;
                this.isKeys = isKeys;
            }

            void ICollection.CopyTo(Array array, int index)  {
                if (array == null)
                    throw new ArgumentNullException("array");
                if (index < 0)
                    throw new ArgumentOutOfRangeException("index");
                for (DictionaryNode node = list.head; node != null; node = node.next) {
                    array.SetValue(isKeys ? node.key : node.value, index);
                    index++;
                }
            }

            int ICollection.Count {
                get {
                    int count = 0;
                    for (DictionaryNode node = list.head; node != null; node = node.next) {
                        count++;
                    }
                    return count;
                }
            }

            bool ICollection.IsSynchronized {
                get {
                    return false;
                }
            }

            object ICollection.SyncRoot {
                get {
                    return list.SyncRoot;
                }
            }

            IEnumerator IEnumerable.GetEnumerator() {
                return new NodeKeyValueEnumerator(list, isKeys);
            }


            private class NodeKeyValueEnumerator: IEnumerator {
                ListDictionary list;
                DictionaryNode current;
                int version;
                bool isKeys;
                bool start;

                public NodeKeyValueEnumerator(ListDictionary list, bool isKeys) {
                    this.list = list;
                    this.isKeys = isKeys;
                    this.version = list.version;
                    this.start = true;
                    this.current = null;
                }

                public object Current {
                    get {
                        if (current == null) {
                            throw new InvalidOperationException("Enumerator is positioned before the first element or after the last element of the collection.");
                        }
                        return isKeys ? current.key : current.value;
                    }
                }

                public bool MoveNext() {
                    if (version != list.version) {
                        throw new InvalidOperationException("Collection was modified after the enumerator was instantiated.");
                    }
                    if (start) {
                        current = list.head;
                        start = false;
                    }
                    else {
                        current = current.next;
                    }
                    return (current != null);
                }

                public void Reset() {
                    if (version != list.version) {
                        throw new InvalidOperationException("Collection was modified after the enumerator was instantiated.");
                    }
                    start = true;
                    current = null;
                }
            }
        }

        private class DictionaryNode {
            public object key;
            public object value;
            public DictionaryNode next;
        }
    }
}

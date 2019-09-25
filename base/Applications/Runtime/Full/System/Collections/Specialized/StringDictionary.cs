//------------------------------------------------------------------------------
// <copyright file="StringDictionary.cs" company="Microsoft">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//------------------------------------------------------------------------------

//
// 
namespace System.Collections.Specialized
{
    using System.Runtime.InteropServices;
    using System.Diagnostics;
    using System;
    using System.Collections;
    using System.Globalization;

    /// <devdoc>
    ///    <para>Implements a hashtable with the key strongly typed to be
    ///       a string rather than an object. </para>
    /// </devdoc>
    public class StringDictionary : IEnumerable {

        internal Hashtable contents = new Hashtable();

        /// <devdoc>
        /// <para>Initializes a new instance of the System.Windows.Forms.StringDictionary class.</para>
        /// </devdoc>
        public StringDictionary() {
        }


        /// <devdoc>
        /// <para>Gets the number of key-and-value pairs in the System.Windows.Forms.StringDictionary.</para>
        /// </devdoc>
        public virtual int Count {
            get {
                return contents.Count;
            }
        }


        /// <devdoc>
        /// <para>Indicates whether access to the System.Windows.Forms.StringDictionary is synchronized (thread-safe). This property is
        ///    read-only.</para>
        /// </devdoc>
        public virtual bool IsSynchronized {
            get {
                return contents.IsSynchronized;
            }
        }

        /// <devdoc>
        ///    <para>Gets or sets the value associated with the specified key.</para>
        /// </devdoc>
        public virtual string this[string key] {
            get {
                if (key == null) {
                    throw new ArgumentNullException("key");
                }

                return (string) contents[key.ToLower()];
            }
            set {
                if (key == null) {
                    throw new ArgumentNullException("key");
                }

                contents[key.ToLower()] = value;
            }
        }

        /// <devdoc>
        /// <para>Gets a collection of keys in the System.Windows.Forms.StringDictionary.</para>
        /// </devdoc>
        public virtual ICollection Keys {
            get {
                return contents.Keys;
            }
        }


        /// <devdoc>
        /// <para>Gets an object that can be used to synchronize access to the System.Windows.Forms.StringDictionary.</para>
        /// </devdoc>
        public virtual object SyncRoot {
            get {
                return contents.SyncRoot;
            }
        }

        /// <devdoc>
        /// <para>Gets a collection of values in the System.Windows.Forms.StringDictionary.</para>
        /// </devdoc>
        public virtual ICollection Values {
            get {
                return contents.Values;
            }
        }

        /// <devdoc>
        /// <para>Adds an entry with the specified key and value into the System.Windows.Forms.StringDictionary.</para>
        /// </devdoc>
        public virtual void Add(string key, string value) {
            if (key == null) {
                throw new ArgumentNullException("key");
            }

            contents.Add(key.ToLower(), value);
        }

        /// <devdoc>
        /// <para>Removes all entries from the System.Windows.Forms.StringDictionary.</para>
        /// </devdoc>
        public virtual void Clear() {
            contents.Clear();
        }

        /// <devdoc>
        ///    <para>Determines if the string dictionary contains a specific key</para>
        /// </devdoc>
        public virtual bool ContainsKey(string key) {
            if (key == null) {
                throw new ArgumentNullException("key");
            }

            return contents.ContainsKey(key.ToLower());
        }

        /// <devdoc>
        /// <para>Determines if the System.Windows.Forms.StringDictionary contains a specific value.</para>
        /// </devdoc>
        public virtual bool ContainsValue(string value) {
            return contents.ContainsValue(value);
        }

        /// <devdoc>
        /// <para>Copies the string dictionary values to a one-dimensional <see cref='System.Array'/> instance at the
        ///    specified index.</para>
        /// </devdoc>
        public virtual void CopyTo(Array array, int index) {
            contents.CopyTo(array, index);
        }

        /// <devdoc>
        ///    <para>Returns an enumerator that can iterate through the string dictionary.</para>
        /// </devdoc>
        public virtual IEnumerator GetEnumerator() {
            return contents.GetEnumerator();
        }

        /// <devdoc>
        ///    <para>Removes the entry with the specified key from the string dictionary.</para>
        /// </devdoc>
        public virtual void Remove(string key) {
            if (key == null) {
                throw new ArgumentNullException("key");
            }

            contents.Remove(key.ToLower());
        }

    }

}

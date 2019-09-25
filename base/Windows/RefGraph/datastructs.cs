// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Text;
using System.Collections;
using Microsoft.Contracts;

namespace DataStructs
{
    using System;
    using System.Text;
    using System.IO;
    using System.Collections;
    using System.Collections.Specialized;
    using System.Diagnostics;


    /// <summary>
    /// Represents an object that can be copied deeply, as opposed to the shallow ICloneable.
    /// </summary>
    public interface ICopyable
    {
        object! Copy();
    }

    public interface ISet : ICollection, ICopyable
    {
        /// <summary>
        /// Checks whether a given element is part of <c>this</c> set.
        /// </summary>
        /// <param name="elem">element searched into the set</param>
        /// <returns><c>true</c> if <c>elem</c> is in the set, <c>false</c> otherwise</returns>
        bool Contains(Object! o);

    }


    /// <summary>
    /// Interface for the set abstraction: collection of distinct elements.
    /// </summary>
    public interface IMutableSet: ISet, ICloneable
    {
        /// <summary>
        /// Adds an element to <c>this</c> set.
        /// </summary>
        /// <param name="elem">element to add</param>
        /// <returns><c>true</c> if <c>this</c> set was modified as a result of this operation</returns>
        /// 
        bool Add(Object! o);

        /// <summary>
        /// Removes an element from <c>this</c> set. 
        /// </summary>
        /// <param name="elem"></param>
        /// <returns><c>true</c> if <c>this</c> set was modified as a result of this operation</returns>
        bool Remove(Object! o);

        /// <summary>
        /// Adds several elements from <c>this</c> set.
        /// </summary>
        /// <param name="eable"><c>IEnumerable</c> that contains the elements to be added</param>
        /// <returns><c>true</c> if <c>this</c> set was modified as a result of this operation</returns>
        bool AddAll(IEnumerable! eable);

        /// <summary>
        /// Removes several elements from <c>this</c> set.
        /// </summary>
        /// <param name="eable"><c>IEnumerable</c> containing the elements to be removed</param>
        /// <returns><c>true</c> if <c>this</c> set was modified as a result of this operation</returns>
        bool RemoveAll(IEnumerable! eable);

        /// <summary>
        /// Deletes all the elements of <c>this</c> set. As a result the <c>Count</c> property will be <c>0</c>.
        /// </summary>
        /// <returns><c>true</c> if <c>this</c> set was modified as a result of this operation</returns>
        bool Clear();

    }

    public delegate IMutableSet! DSetFactory();
    public delegate IDictionary! DDictionaryFactory();

    /// <summary>
    /// Summary description for DataStructsUtil.
    /// </summary>
    public abstract class DataStructUtil
    {   
        public static readonly DSetFactory! DefaultSetFactory = new DSetFactory(default_set_factory);
        private static IMutableSet! default_set_factory()
        {
            return new HashSet(1);
        }


        public static readonly DSetFactory! SmallSetFactory = new DSetFactory(small_set_factory);
        private static IMutableSet! small_set_factory()
        {
            return new ArraySet(1);
        }


        public static readonly DDictionaryFactory! DefaultDictionaryFactory = new DDictionaryFactory(default_dict_factory);
        private static IDictionary! default_dict_factory()
        {
            return new Hashtable(1);
        }
        

        public static readonly DDictionaryFactory! SmallDictionaryFactory = new DDictionaryFactory(small_dict_factory);
        private static IDictionary! small_dict_factory()
        {
            return new ListDictionary();
        }
        

        public static ISet! EMPTY_SET = new ImmutableSetWrapper(new HashSet());

        public static ISet singleton(object! elem)
        {
            return new SingletonSet(elem);
        }


        public static IList SortedCollection(ICollection! coll)
        {
            return SortedCollection(coll, null);
        }

        public static IList SortedCollection(ICollection! coll,  IComparer comp)
        {
            ArrayList al = new ArrayList(coll);
            if (comp == null)
                al.Sort();
            else
                al.Sort(comp);
            return al;
        }

        /// <summary>
        /// Produces a string representation of an <c>IEnumerable</c> object,
        /// using <c>o2s</c> to produce the string representation of each
        /// element.
        /// </summary>
        /// <param name="eable"></param>
        /// <param name="o2s"></param>
        /// <returns></returns>
        /// 
        public static string! IEnum2String(IEnumerable! eable,  DObj2String o2s)
        {
            StringBuilder buff = new StringBuilder();
            buff.Append("[");
            bool first = true;
            foreach (object o in eable) {
                if (first) first = false;
                else buff.Append(",");
                if (o2s != null)
                    buff.Append(o2s(o));
                else
                    buff.Append(o);
            }
            buff.Append("]");
            return buff.ToString();
        }


    }

    /// <summary>
    /// Conversion object -> string. Useful for classes for which we cannot
    /// modify / override the <c>ToString</c> method. A <c>null</c> value
    /// should be interpreted as the classic <c>ToString</c> method.
    /// </summary>
    public delegate string DObj2String(object obj);

    internal class SingletonSet: ISet
    {
        private object! elem;

        public SingletonSet(object! elem)
        {
            this.elem = elem;
        }

        public bool Contains(object! elem)
        {
            return this.elem.Equals(elem);
        }

        public int Count { 
            [Pure]
            get { return 1; } }

        public override int GetHashCode()
        {
            return elem.GetHashCode();
        }

        public IEnumerator GetEnumerator()
        {
            return new SingletonEnumerator(elem);
        }

        private class SingletonEnumerator: IEnumerator
        {
            private object elem;
            private int index = -1;

            [NotDelayed]
            public SingletonEnumerator(object elem)
            {
                this.elem = elem;
                Reset();
            }

            public virtual object Current
            {
                get 
                {
                    if (index == 0) return elem;
                    else
                        throw new InvalidOperationException();
                }
            }

            public virtual bool MoveNext()
            {
                switch (index) {
                    case -1:
                        index++;
                        return true;
                    case 0:
                        index++;
                        return false;
                    case 1:
                    default:
                        return false;
                }
            }

            public virtual void Reset()
            {
                index = -1;
            }
        }

        public object! Copy()
        {
            SingletonSet copy = (SingletonSet) this.MemberwiseClone();
            assert(copy != null);
            copy.elem = (this.elem is ICopyable) ? ((ICopyable) this.elem).Copy() : this.elem;
            return copy;
        }

        void ICollection.CopyTo (Array! target, int index) 
        {
            assume(target != null);
            target.SetValue(this.elem, index);
        }

        object! ICollection.SyncRoot
        {
            [Pure]
            get 
            {
                return this;
            }
        }

        bool ICollection.IsSynchronized 
        {
            [Pure]
            get { return false; }
        }
    }
    
    
    
    public class OneToManyMap/*<KEY,ELEM>*/ : Hashtable//<KEY,ArrayList<ELEM>>  
    {
        public override void Add (Object! key, Object newItem)
        {
            ArrayList items = base[key] as ArrayList;
            if (items == null) {
                items = new ArrayList();
                base[key] = items;
            }
            items.Add(newItem);
        }


        public virtual bool Contains (Object! key, Object item)
        {
            ArrayList items = base[key] as ArrayList;
            if (items == null)
                return false;
            return items.Contains(item);
        }


        public new ArrayList/*<Object>*/ this [Object! key] 
        {
            get { return base[key] as ArrayList; }
            set { base[key] = value; }
        }

    }



    public class DoubleTable/*<KEY1,KEY2,ELEM>*/ : Hashtable//<KEY1,Hashtable<KEY2,ELEM>>  
    {
        public DoubleTable () : base() { }

        private DoubleTable (Hashtable table) : base(table) { }


        public new Hashtable this [object! key]
        {
            get 
            {
                return base[key] as Hashtable;
                //
                //  if (table == null) {
                //      table = new Hashtable();
                //      base[key] = table;
                //  }
                //  return table;
                //    
            }

            set
            {
                base[key] = value;
            }
        }


        public void Insert (object! key1, object! key2, object element)
        {
            Hashtable table = this[key1];
            if (table == null) {
                table = new Hashtable();
                this[key1] = table;
            }
            table[key2] = element;
        }


        
        public object Lookup (object! key1, object! key2) 
        {
            Hashtable range = this[key1];
            if (range != null) {
                return range[key2];
            }
            else {
                return null;
            }
        }
        
        public override object! Clone ()
        {
            // careful. We have to deep clone the targets of the underlying hashtable.
            DoubleTable copy = new DoubleTable();
            foreach (object key in (IEnumerable!)this.Keys) {
                Hashtable x = this[key];

                assert(x != null);
                copy.Add(key, x.Clone());
            }
            return copy;
        }

        public DoubleTable Copy() 
        {
            return (DoubleTable)this.Clone();
        }
    }


    
    
    /// <summary>
    /// An attempt to make coding with datatypes more pleasant in C#
    /// </summary>
    /// <remarks>
    /// Use <c>Datatype</c> as a base class on each of your abstract data type base classes. When doing
    /// case analysis on such a value, use the method <c>Tag</c> to get a String representation of the 
    /// dynamic class name. This can be matched in the <c>case</c> branches of a switch. 
    /// <p>
    /// For pairwise matching, use <c>x.Tag + y.Tag</c> and <c>case "Foo"+"Bar"</c>.</p>
    /// <p>
    /// Can be extended to compute the set of tags of each abstract datatype instance and utility methods.</p>
    /// </remarks>
    public abstract class Datatype 
    {
        private int tag;

        private static Hashtable!/*<Type,DatatypeInfo>*/ typeTable = new Hashtable();

        private class DatatypeInfo 
        {
            IList!/*<Type>*/ members;
            Type abstractBaseType;
            public DatatypeInfo(Type abstractBaseType) 
            {
                members = new ArrayList();
                this.abstractBaseType = abstractBaseType;
            }

            public void Add(Type variant) 
            {
                members.Add(variant);
            }

            public ICollection! Members { get { return members; } }
        }

        
        private void AddToTable (Type! variant) 
        {
            DatatypeInfo info = GetBaseInfo(variant);
            info.Add(variant);
            typeTable[variant] = info;
        }

        
        private DatatypeInfo! GetBaseInfo (Type! variant) 
        {
            Type abase = FindBase(variant);
            DatatypeInfo info = (DatatypeInfo)Datatype.typeTable[abase];
            if (info == null) {
                // first time we see anything in this class tree.
                info = new DatatypeInfo(abase);
                Datatype.typeTable[abase] = info;
            }
            return info;
        }

        
        private Type! FindBase(Type! variant) 
        {
            Type abase = variant.BaseType;
            assume(abase != null);
            if (abase.IsAbstract) {

                // check that it is not datatype
                if (abase == typeof(Datatype)) {
                    Debug.Assert(false, "Every datatype should have an abstract base class that is a subtype of Datatype: " + variant.Name + " does not.");
                }

                // check if its base is Datatype
                if (abase.BaseType == typeof(Datatype)) {
                    return abase;
                }
                else {
                    // intermediate abstract base
                    return FindBase(abase);
                }
            }
            // recurse until we find abstract base
            return FindBase(abase);
        }

        [NotDelayed]
        protected Datatype (int tag) 
        {
            Type realType = this.GetType();
            assume(realType != null);
            this.tag = tag; //realType.Name;
            if (typeTable[realType] == null) {
                // add this first instance to the type table
                this.AddToTable(realType);
            }
        }

        public virtual int Tag
        {
            get { return tag; }
        }

        public void IncompleteMatch() 
        {
            Type realType = this.GetType();
            assume(realType != null);
            DatatypeInfo info = (DatatypeInfo)Datatype.typeTable[realType];

            assert(info != null);

            System.Text.StringBuilder buffer = new StringBuilder();
            foreach (object member in info.Members) {
                Type m = member as Type;

                assert(m != null);

                buffer.Append(" ");
                buffer.Append(m.Name);
            }

            Console.Write("Incomplete match: {0} was not matched.\nDatatype contains the following variants {1}\n",
                this.Tag, buffer.ToString());
            Debug.Assert(false, "incomplete match");
        }
    }

    public class ConvertingEnumerable : IEnumerator, IEnumerable
    {
        public delegate object ObjectConverter(object o);

        private IEnumerator! underlying;
        private ObjectConverter! objConverter;

        [NotDelayed]
        public ConvertingEnumerable(IEnumerable! underlying, ObjectConverter! objConverter)
        {
            this.underlying = underlying.GetEnumerator();
            this.objConverter = objConverter;
            base();
            Reset();
        }

        public object Current
        {
            get 
            {
                return objConverter(underlying.Current);
            }
        }

        public bool MoveNext()
        {
            return underlying.MoveNext();
        }

        public void Reset()
        {
            underlying.Reset();
        }

        public IEnumerator GetEnumerator()
        {
            return this;
        }
    }

}

namespace DataStructs
{
    using System;
    using System.Text;
    using System.Collections;



    public abstract class Set
    {
        public static ISet Difference(IEnumerable! a, ISet! b)
        {
            IMutableSet diff = new HashSet();
            foreach (object elem in a)
                if(!b.Contains(elem))
                    diff.Add(elem);
            return diff;
        }


        public static ISet Union(ISet! a, ISet! b)
        {
            IMutableSet union = new HashSet(a);
            union.AddAll(b);
            return union;
        }


        public static ISet Intersect(ISet! a, ISet! b) 
        {
            IMutableSet inter = new HashSet();

            if (a.Count < b.Count) {
                ISet c = a;
                a = b;
                b = c;
            }
            foreach (object elem in a) {
                if (b.Contains(elem)) {
                    inter.Add(elem);
                }
            }   
            return inter;
        }

        
        /// <summary>
        /// Returns null if A included in B. Otherwise, returns an element in
        /// A that is not in B.
        /// </summary>
        
        public static object NonSubsetWitness(ISet! a, ISet! b)
        {
            foreach (object elem in a) {
                if (!b.Contains(elem)) {
                    return elem;
                }
            }
            return null;
        }


        public delegate bool SetFilter(object! obj);

        public static ISet Filter(ISet! a, SetFilter! filter) 
        {
            IMutableSet inter = new HashSet();

            foreach (object elem in a) {
                if (filter(elem)) {
                    inter.Add(elem);
                }
            }   
            return inter;
        }


        public static readonly ISet Empty = new ArraySet(0);
    }



    public abstract class AbstrSet: IMutableSet
    {
        public abstract bool Add(object! elem);
        public virtual bool AddAll(IEnumerable! eable) 
        {
            bool modified = false;
            foreach (object elem in eable)
                if(Add(elem)) modified = true;
            return modified;
        }

        public abstract bool Remove(object! elem);

        public virtual bool RemoveAll(IEnumerable! eable)
        {   
            ISet iset = eable as ISet;
            if ((iset != null) && (iset.Count > 2 * this.Count)) {
                // optimized code for the special case when eable is a large ISet
                ArrayList to_remove = new ArrayList();
                foreach (object elem in this)
                    if(iset.Contains(elem))
                        to_remove.Add(elem);
                if (to_remove.Count != 0) {
                    foreach (object elem in to_remove)
                        this.Remove(elem);
                    return true;
                }
                return false;
            }
            
            bool modified = false;
            foreach (object elem in eable)
                if(Remove(elem)) modified = true;
            return modified;
        }           


        public abstract bool Contains(object! elem);
        public abstract bool Clear();
        public abstract int Count { get; }


        public abstract IEnumerator GetEnumerator();

        public virtual void CopyTo(Array! array, int index) 
        {
            foreach (object o in this) 
                array.SetValue(o, index++);
        }


        void ICollection.CopyTo(Array! a, int index) { 
            Array! b = a;
            this.CopyTo(b, index);
        }



        [Confined]
        public override string! ToString()
        {
            return DataStructUtil.IEnum2String(this, null);
        }

        public override int GetHashCode()
        {
            throw new InvalidOperationException("GetHashCode is unimplemented");
        }

        [Confined]
        public override bool Equals(object o)
        {
            ISet iset2 = o as ISet;
            // if o is not an ISet, is a set with a different number of
            // elements, obviously o != this 
            if ((iset2 == null) ||
                (iset2.Count != this.Count))
                return false;
            foreach (object elem in this)
                if(!iset2.Contains(elem))
                    return false;
            return true;
        }

        public virtual bool IsSynchronized { get { return false; } }
        
        public virtual object! SyncRoot {  [Pure] get { return this; } }

        public abstract object! Clone();

        object ICloneable.Clone() { 
            return this.Clone();
        }

        public abstract object! Copy();
    }



    public class ArraySet : AbstrSet
    {
        public ArraySet(int initial_size)
        {
            array = new object[initial_size];
        }

        public ArraySet(object singleton) 
        {
            array = new object[] {singleton};
            count = 1;
        }

        public ArraySet() : this(5) { }

        private object[]! array;
        private int count = 0;

        public override bool Add(object! elem)
        {
            assert(elem != null);

            for (int i = 0; i < count; i++)
                if(elem.Equals(array[i]))
                    return false;
            if (count == array.Length) {
                object[] array2 = new object[count*2];
                for (int i = 0; i < count; i++)
                    array2[i] = array[i];
                array = array2;
            }
            array[count++] = elem;
            return true;
        }

        public override bool Remove(object! elem)
        {
            assert(elem != null);

            for (int i = 0; i < count; i++)
                if(elem.Equals(array[i]))
                {
                    if (i < count - 1)
                        array[i] = array[count-1];
                    // no memory leaks
                    array[count-1] = null;
                    count--;
                    return true;
                }
            return false;
        }

        public override bool Contains(object! elem)
        {
            assert(elem != null);

            for (int i = 0; i < count; i++)
                if(elem.Equals(array[i]))
                    return true;
            return false;
        }

        public override bool Clear()
        {
            bool result = count > 0;
            count = 0;
            return result;
        }

        public override int Count { get { return count; } }

        public override IEnumerator GetEnumerator()
        {
            return new ArrayEnumerator(array, count);
        }

        public override object! Clone()
        {
            ArraySet set2 = (ArraySet) this.MemberwiseClone();
            assume(set2 != null);
            set2.array = (object[]) this.array.Clone();
            return set2;
        }

        public override object! Copy()
        {
            ArraySet set2 = (ArraySet) this.MemberwiseClone();
            assume(set2 != null);

            set2.array = (object[]) this.array.Clone();
            for (int i = 0; i < set2.count; i++) {
                ICopyable elem = set2.array[i] as ICopyable;
                if (elem != null)
                    set2.array[i] = elem.Copy();
            }
            return set2;
        }

    }



    public class ImmutableSetWrapper: IMutableSet
    {
        private ISet! real_set;

        public ImmutableSetWrapper(ISet! s)
        {
            real_set = s;
        }

        public bool Add(object! key)
        {
            throw new ModifyImmutableCollException();
        }

        
        public bool AddAll(IEnumerable! keys)
        {
            throw new ModifyImmutableCollException();
        }


        public bool Remove(object! key)
        {
            throw new ModifyImmutableCollException();
        }


        public bool RemoveAll(IEnumerable! keys)
        {
            throw new ModifyImmutableCollException();
        }


        public bool Clear()
        {
            throw new ModifyImmutableCollException();
        }
        

        public object Clone()
        {
            // memberwise clone is enough because no destructive operations
            // are allowed on this kind of objects.
            return this.MemberwiseClone();
        }

        public bool Contains(object! key)
        {
            return real_set.Contains(key);
        }

        public IEnumerator GetEnumerator()
        {
            return real_set.GetEnumerator();
        }

        public override int GetHashCode()
        {
            return real_set.GetHashCode();
        }

        public int Count { 
            [Pure]
            get { return real_set.Count; } }

        void ICollection.CopyTo(Array! target, int index) 
        {
            this.real_set.CopyTo(target, index);
        }

        bool ICollection.IsSynchronized 
        {
            [Pure]
            get { return this.real_set.IsSynchronized; }
        }

        object! ICollection.SyncRoot 
        {
            [Pure]
            get { return this.real_set.SyncRoot; }
        }

        public object! Copy()
        {
            ImmutableSetWrapper copy = (ImmutableSetWrapper) this.MemberwiseClone();
            assume(copy != null);

            // ISet implements ICopyable so we always do a deep copy of real_set
            copy.real_set = (ISet) this.real_set.Copy();
            return copy;
        }


    }


    public class ModifyImmutableCollException: SystemException
    {
        public ModifyImmutableCollException():
            base("Attempt to modify an immutable collection") {}
    }



    /// <summary>
    /// Full implementation of the <c>ISet</c> interface, backed by a <c>Hashtable</c>.
    /// </summary>
    /// <remarks>
    /// As each <c>HashSet</c> is backed by a
    /// <see cref="System.Collections.Hashtable">Hashtable</see>, all requirements that
    /// apply for the <c>Hashtable</c> keys apply for the elements of a <c>HashSet</c>
    /// as well.
    ///
    /// <p>The <c>HashSet</c> class overrides the methods
    /// <see cref="GetHashCode">GetHashCode</see> and <see cref="Equals">Equals</see>
    /// (inherited from <see cref="System.Object">Object</see>) in order to provide
    /// structural equality:
    /// two sets are equal iff they contain the same elements (where the semantics of "same"
    /// is defined by the <c>Equals</c> method of those objects).  You can put HashSets into
    /// HashSets; however, to avoid infinite loops, you should never insert a <c>HashSet</c>
    /// into itself.
    /// The hashcode of a <c>HashSet</c> is defined as the "xor" of the hashcodes of the set
    /// elements. </p>
    /// 
    /// <p>
    /// The <c>GetHashCode</c> function of a <c>HashSet</c> executes in <c>O(1)</c> time:
    /// the hashcode is dynamically updated after each operation that modifies the set.
    /// If the hashcode functions used for all the other involved objects is good and
    /// is computed in <c>O(1)</c> time, one element addition and removal execute in
    /// <c>O(1)</c> time; <c>Equals</c> works in time linear to the number of elements of
    /// <c>this</c> set.
    /// </p> 
    /// </remarks>
    public class HashSet: AbstrSet
    {
        // the Hashtable that backs up the implementation of this HashSet
        // an element is in the set if it's a key in the Hashtable
        protected Hashtable! hash;

        private Hashtable! Hash { get { return this.hash; } }

        // all keys are associated with the bogus value VALUE
        protected static object VALUE = new object();

        /// <summary>
        /// Constructs an empty <c>HashSet</c>.
        /// </summary>
        public HashSet() : this(0)
        {
        }

        public HashSet(int initialsize)
        {
            if (initialsize != 0) {
                hash = new Hashtable(initialsize);
            }
            else {
                hash = new Hashtable();
            }
            set_hash_code = 0;
            base();
        }

        
        /// <summary>
        /// Constructs a <c>HashSet</c> initialized to contain all
        /// elements from an <c>IEnumerable</c>.
        /// </summary>
        public HashSet(IEnumerable! eable) : this()
        {
            AddAll(eable);
        }

        public override bool Contains(object! elem)
        {
            return hash.ContainsKey(elem);
        }

        public override bool Add(object! elem) 
        {
            if (elem == null)
                throw new ApplicationException("null set element");

            // element already present in the set
            if (hash.ContainsKey(elem)) return false;
            // new element!
            hash[elem] = VALUE;
            set_hash_code ^= elem.GetHashCode();
            return true;
        }

        public override bool Remove(object! elem)
        {
            assert(elem != null);

            if (!hash.ContainsKey(elem)) return false;
            hash.Remove(elem);
            // a^b^b = a; we eliminate the influence of "elem" on the
            // hash code for the entire set
            set_hash_code ^= elem.GetHashCode();
            return true;
        }

        public override bool Clear()
        {
            set_hash_code = 0;
            bool result = (this.Count != 0);
            hash.Clear();
            return result;
        }

        public override int Count { get { return hash.Count; } }

        protected class HashSetEnumerator: IEnumerator 
        {
            HashSet! hash_set;
            IEnumerator! hash_e;

            public HashSetEnumerator(HashSet! hash_set) 
            {
                this.hash_set  = hash_set;
                this.hash_e    = hash_set.Hash.GetEnumerator();
                base();
            }
            
            public object Current
            {
                get
                {
                    DictionaryEntry de = (DictionaryEntry)hash_e.Current;
                    return de.Key;
                }
            }

            public bool MoveNext() 
            {
                return hash_e.MoveNext();
            }

            public void Reset() 
            {
                hash_e.Reset();
            }
        }


        
        public override IEnumerator GetEnumerator() 
        {
            return new HashSetEnumerator(this);
        }
        
        public override int GetHashCode()
        {
            return set_hash_code;
        }
        // hash_code of this set; dynamically maintained after each
        // operation on this set
        protected int set_hash_code;

        // Copy constructor
        private HashSet(HashSet! old, bool deep) : this(old.Count) {
            foreach (object elem in old) {
                if (deep) { 
                    this.Add(elem);
                }
                else {
                    this.Add((elem is ICopyable) ? ((ICopyable) elem).Copy() : elem);
                }
            }
        }

        public override object! Clone()
        {
            return new HashSet(this, false);
        }

        public override object! Copy()
        {
            return new HashSet(this, true);
        }
    }
}

namespace DataStructs
{

    public interface IRelation 
    {
        bool ContainsKey(object! key);

        bool Contains(object! key, object! value);

        ICollection! GetKeys();

        ISet! GetValues(object! key);

        IRelation! Reverse();
    }


    public interface IMutableRelation : IRelation, ICloneable, ICopyable
    {
        bool Add(object! key, object! value);

        bool AddAll(object! key, IEnumerable! values);

        /// <summary>
        /// Adds an entire relation to <d>this</d> relation.
        /// </summary>
        /// <param name="relation">Relation that is unioned with this relation.</param>
        /// <returns><c>true</c> iff <c>this</c> relation changed.</returns>
        bool AddRelation(IRelation! relation);

        bool Remove(object! key, object! value);
        bool RemoveAll(object! key, IEnumerable! values);

        bool RemoveKey(object! key);
        bool RemoveSeveralKeys(IEnumerable! keys); 

        bool RemoveSeveralValues(IEnumerable! values);

        new
        IMutableRelation! Reverse();

    }


    /// <summary>
    /// Full <c>IMutableRelation</c> implementation.
    /// </summary>
    public class Relation: IMutableRelation
    {
        /// <summary>
        /// Full power relation constructor that allows you to finely tune the memory consumption.
        /// Internally, a relation is a dictionary that assigns to each key the set of values that are
        /// in relation with it.  This constructor allows you to specify the dictionary and the set
        /// factory.
        /// </summary>
        /// <param name="dict_fact">Dictionary factory used to construct the underlying dictionary.</param>
        /// <param name="set_fact">Set factory used to construct the set that will store the values
        /// assoctiated with each key.</param>
        public Relation(DDictionaryFactory! dict_fact, DSetFactory! set_fact)
        {
            this.dict_fact = dict_fact;
            this.set_fact  = set_fact;
            this.hash = dict_fact();
            base();
        }

        /// <summary>
        /// Default constructor.  Uses the default factory for dictionaries (i.e., equiv. to new Hashtable())
        /// and sets (i.e., equiv. to new HashSet()).
        /// </summary>
        public Relation() :
            this(DataStructUtil.DefaultDictionaryFactory, DataStructUtil.DefaultSetFactory) {}

        private readonly DDictionaryFactory! dict_fact;
        private readonly DSetFactory!        set_fact;

        // underlying structure that stores the information attached with this relation
        private IDictionary! hash/*<object, ISet<object>>*/;

        public virtual bool Add(object! key, object! value)
        {
            return get_set_for_add(key).Add(value);
        }

        public virtual bool AddAll(object! key, IEnumerable! values)
        {
            return get_set_for_add(key).AddAll(values);
        }

        public virtual bool AddRelation(IRelation! relation)
        {
            if (relation == null) return false;
            bool changed = false;
            foreach (object key in relation.GetKeys())
                if(this.AddAll(key, relation.GetValues(key)))
                    changed = true;
            return changed;
        }

        private IMutableSet! get_set_for_add(object! key)
        {
            IMutableSet s = (IMutableSet) hash[key];
            if (s == null) {
                s = set_fact();
                hash[key] = s;
            }
            return s;
        }

        public virtual ISet! GetValues(object! key)
        {
            ISet s = (ISet) hash[key];
            if (s == null)
                s = DataStructUtil.EMPTY_SET;
            else
                s = new ImmutableSetWrapper(s);
            return s;
        }

        public virtual bool ContainsKey(object! key)
        {
            return hash.Contains(key);
        }

        public virtual bool Contains(object! key, object! value)
        {
            return ((ISet) GetValues(key)).Contains(value);
        }

        public virtual bool Remove(object! key, object! value)
        {
            IMutableSet s = (IMutableSet) hash[key];
            if (s == null)
                return false;

            bool result = s.Remove(value);
            if (s.Count == 0)
                hash.Remove(key);

            return result;
        }

        public virtual bool RemoveAll(object! key, IEnumerable! values)
        {
            IMutableSet s = (IMutableSet) hash[key];
            if (s == null)
                return false;

            bool result = s.RemoveAll(values);
            if (s.Count == 0)
                hash.Remove(key);

            return result;
        }


        public virtual bool RemoveKey(object! key)
        {
            if (hash.Contains(key)) {
                hash.Remove(key);
                return true;
            }
            return false;
        }

        public virtual bool RemoveSeveralKeys(IEnumerable! keys)
        {
            ISet iset_keys = keys as ISet;
            if (iset_keys != null) {
                ICollection keys_of_this = this.GetKeys();
                if (iset_keys.Count > 2 * keys_of_this.Count) {
                    // optimized code for the special case when "keys" is a large ISet
                    // UGLY code! comodif. + IEnumerator has no remove method
                    ArrayList to_remove = new ArrayList();
                    foreach (object key in keys_of_this)
                        // set membership is O(1) :)
                        if (iset_keys.Contains(key))
                            to_remove.Add(key);
                    if (to_remove.Count > 0) {
                        foreach (object key in to_remove)
                            hash.Remove(key);
                        return true;
                    }
                    return false;
                }

            }

            bool modified = false;
            foreach (object key in keys)
                if(hash.Contains(key))
                {
                    hash.Remove(key);
                    modified = true;
                }
            return modified;
        }


        public virtual bool RemoveSeveralValues(IEnumerable! values)
        {
            bool modified = false;

            // the following code is inneficient ... this is due to:
            // 1. the need to avoid Comodification exceptions
            // 2. the lack of a remove method in IEnumerator()
            ArrayList keys = new ArrayList(GetKeys());
            foreach (object key in keys) {
                IMutableSet s = (IMutableSet) hash[key];
                assert(s != null);
                if (s.RemoveAll(values)) {
                    modified = true;
                    if (s.Count == 0)
                        hash.Remove(key);
                }
            }

            return modified;
        }

        
        public virtual ICollection! GetKeys()
        {
            return (ICollection!)hash.Keys;
        }

        public virtual IMutableRelation! Reverse()
        {
            IMutableRelation reverse = new Relation();
            foreach (object key in GetKeys())
                foreach(object value in GetValues(key))
                    reverse.Add(value, key);
            return reverse;
        }

        IRelation! IRelation.Reverse() 
        {
            return this.Reverse();
        }

        /// Copy constructor
        private Relation(Relation! old, bool deep) : this(old.dict_fact, old.set_fact)
        {
            foreach (object key in old.GetKeys()) {
                // deep copy of the key, if requested && possible
                object key2 = (deep && key is ICopyable) ? ((ICopyable) key).Copy() : key;
                foreach (object val in old.GetValues(key)) {
                    // deep copy of the value, if requested && possible
                    object val2 = (deep && val is ICopyable) ? ((ICopyable) val).Copy() : val;
                    this.Add(key2, val2);
                }
            }
        }

        /// <summary>
        /// "Shallow" copy of a relation.  Produces an independent copy of <c>this</c> <c>Relation</c>.
        /// The keys and values are not duplicated.  Operations on the
        /// resulting <c>Relation</c> and on <c>this</c> <c>Relation</c> don't interact.
        /// </summary>
        /// <returns>An independent copy of <c>this</c> Relation.</returns>
        public virtual object Clone()
        {
            return new Relation(this, false);
        }

        /// <summary>
        /// Deep copy of a relation.  Produces an independent copy of <c>this</c> <c>Relation</c>,
        /// in which even the keys and values are duplicated (using deep copy) if they implement
        /// the ICopyable interface.  Operations on the resulting <c>Relation</c> and on <c>this</c>
        /// <c>Relation</c> don't interact.
        /// </summary>
        /// <returns>A really deep copy of <c>this</c> <c>Relation</c>.</returns>
        public virtual object! Copy()
        {
            return new Relation(this, true);
        }


        [Confined]
        public override string! ToString()
        {
            StringBuilder sb = new StringBuilder();
            sb.Append("[");
            foreach (object key in this.GetKeys()) {
                sb.Append("\n  ");
                sb.Append(key);
                sb.Append(" -> " );
                sb.Append(this.GetValues(key));
            }
            sb.Append("]");
            return sb.ToString();
        }

        public static Hashtable/*<Key,Value[]>*/ Compact(IRelation!/*<Key,Value>*/ irel, Type! value_type) 
        {
            Hashtable hash = new Hashtable();
            foreach (object key in irel.GetKeys()) {
                ISet vals = irel.GetValues(key);
                if (vals.Count == 0)
                    continue;
                System.Array array_vals = System.Array.CreateInstance(value_type, vals.Count);
                vals.CopyTo(array_vals, 0);
                hash.Add(key, array_vals);
            }
            return hash;
        }
    }

}

namespace DataStructs
{
    using System;
    using System.Text;
    using System.Collections;
    using System.Diagnostics;


    
    
    /// <summary>
    /// Interface for Strongly Connected Methods.
    /// </summary>
    public interface IStronglyConnectedComponent
    {
        /// <summary>
        /// Returns the nodes contained into <c>this</c> StronglyConnectedComponent.
        /// </summary>
        IEnumerable! Nodes { get; }

        bool Contains (object! node);

        /// <summary>
        /// Returns the number of nodes in <c>this</c> StronglyConnectedComponent.
        /// </summary>
        /// <returns></returns>
        int Size { get; }

        /// <summary>
        /// Returns the SCCs that are end points of the arcs that starts in
        /// <c>this</c> StronglyConnectedComponent, i.e., the successors of <c>this</c> StronglyConnectedComponent in the
        /// component graph. Does not contain <c>this</c> StronglyConnectedComponent.
        /// </summary>
        IEnumerable! NextComponents { get; }

        /// <summary>
        /// Returns the SCCs that are starting points for arcs that end
        /// in <c>this</c> StronglyConnectedComponent, i.e., the predecessors of <c>this</c> StronglyConnectedComponent
        /// in the component graph. Does not contain <c>this</c> StronglyConnectedComponent.
        /// </summary>
        IEnumerable! PreviousComponents { get; }
        /// <summary>
        /// Checks whether <c>this</c> StronglyConnectedComponent is a cycle, i.e., if it has more than
        /// one node or it has a single node which points to itself.  The only
        /// StronglyConnectedComponent that does not contain a cycle is a StronglyConnectedComponent composed of a single node
        /// which doesn't point to itself.
        /// </summary>
        /// <returns></returns>
        bool ContainsCycle { get; }

        /// <summary>
        /// Detailed text representation of <c>this</c> StronglyConnectedComponent.
        /// <c>ToString</c> will return just a unique text id of the StronglyConnectedComponent,
        /// while the detailed text representation will be produced by
        /// <c>FullToString</c>
        /// </summary>
        /// <returns></returns>
        string! FullToString();
    }



    /// <summary>
    /// StronglyConnectedComponent is a full implementation of the interface <c>ISCC</c>.
    /// It comes with a producer static method that constructs the
    /// component graph for a given graph. 
    /// </summary>
    public sealed class StronglyConnectedComponent: IStronglyConnectedComponent
    {
        // unique numeric id for debug purposes 
        private int id;

        private IMutableSet! nodes     = new HashSet();
        private IMutableSet! next_SCCs = new HashSet();
        private IMutableSet! prev_SCCs = new HashSet();
        private bool contains_cycle = true;


        // SCCs should be created only by Util.ConstructSCCs
        private StronglyConnectedComponent () { }

        private StronglyConnectedComponent (int id)
        {
            this.id = id;
        }


        public IEnumerable! Nodes { get { return this.nodes; } }


        public bool Contains (object! node)
        {
            return nodes.Contains(node);
        }


        public int Size { get { return this.nodes.Count; } }


        public IEnumerable! NextComponents { get { return this.next_SCCs; } }


        public IEnumerable! PreviousComponents { get { return this.prev_SCCs; } }


        public bool ContainsCycle { get { return this.contains_cycle; } }


        /// <summary>
        /// Detailed text representation of <c>this</c> StronglyConnectedComponent.
        /// </summary>
        /// <returns></returns>
        public string! FullToString ()
        {
            StringBuilder buff = new StringBuilder();
            buff.Append(this);
            buff.Append(" (");
            buff.Append(Size);
            buff.Append(") {\n");
            buff.Append(" Nodes: ");
            buff.Append(Nodes);
            buff.Append("\n");
            buff.Append(" ContainsCycle: ");
            buff.Append(ContainsCycle);
            buff.Append("\n");
            if (next_SCCs.Count > 0) {
                buff.Append(" Next: ");
                buff.Append(NextComponents);
                buff.Append("\n");
            }
            if (prev_SCCs.Count > 0) {
                buff.Append(" Prev: ");
                buff.Append(PreviousComponents);
                buff.Append("\n");
            }
            buff.Append("}");
            return buff.ToString();
        }

        /// <summary>
        /// Simplified text representation for debug purposes: "StronglyConnectedComponent" + numeric id.
        /// </summary>
        /// <returns></returns>
        [Confined]
        public override string! ToString()
        {
            return "StronglyConnectedComponent" + id;
        }


        /// <summary>
        /// Use the <c>nav</c> navigator to explore the graph rooted in the
        /// objects from the <c>roots</c> set, decomposes it into strongly
        /// connected components. Returns the set of strongly connected components.
        /// </summary>
        public static IEnumerable!/*<StronglyConnectedComponent>*/ ConstructSCCs(IEnumerable! roots, IGraphNavigator! navigator)
        {
            return (new SCCFactory(navigator)).ConstructSCCs(roots);
        }

        // private class that does the actual job behind ConstructSCCs
        private sealed class SCCFactory
        {
            public SCCFactory (IGraphNavigator! navigator) { this.navigator = navigator; base(); }

            public IEnumerable!/*<StronglyConnectedComponent>*/ ConstructSCCs (IEnumerable! roots)
            {
                
#if DEBUG_GRAPH
                Console.WriteLine("ConstructSCCs doing 1st dfs...");
#endif
                GraphUtil.SearchDepthFirst(
                    roots,
                    navigator,
                    null,
                    null,
                    null,
                    new DNodeVisitor(first_dfs_end_visitor)
                );

#if DEBUG_GRAPH
                Console.WriteLine("ConstructSCCs doing 2nd dfs...");
#endif

                GraphUtil.SearchDepthFirst(
                    nodes_desc_order,
                    new BackwardGraphNavigator(navigator),
                    new DNodePredicate(second_dfs_avoid),
                    new DNodeVisitor(create_new_SCC),
                    new DNodeVisitor(second_dfs_begin_visitor),
                    null
                );

#if DEBUG_GRAPH
                Console.WriteLine("ConstructSCCs doing put_arcs...");
#endif
                put_arcs();

                return all_SCCs;
            }


            // navigator through the graph
            private IGraphNavigator! navigator;
            // the nodes in the subgraph rooted in the roots
            private IMutableSet!  nodes_in_graph = new HashSet();
            // holds all the nodes in the explored subgraph; the top of the stack
            // is the node whose dfs traversal finished last 
            private Stack! nodes_desc_order = new Stack();

            private StronglyConnectedComponent current_scc = null;
            private ArrayList! all_SCCs = new ArrayList();
            private Hashtable!/*<object,StronglyConnectedComponent>*/ node2scc = new Hashtable();

            // numeric id used to generate distinct ids for the generated SCCs
            private int scc_id = 0;

            private void first_dfs_end_visitor(object! node)
            {
                nodes_in_graph.Add(node);
                nodes_desc_order.Push(node);
            }

            // the second dfs will avoid the nodes that are not in the subgraph rooted
            // in the root nodes; this way, the reversed navigator cannot lead us to
            // unexplored regions.
            private bool second_dfs_avoid (object! node)
            {
                return ! nodes_in_graph.Contains(node);
            }

            private void create_new_SCC (object! node)
            {
                current_scc = new StronglyConnectedComponent(scc_id++);
                all_SCCs.Add(current_scc);
            }

            private void second_dfs_begin_visitor (object! node)
            {
                assert current_scc != null;
                current_scc.nodes.Add(node);
                node2scc.Add(node, current_scc);
            }


            private void put_arcs()
            {
                foreach (object node in nodes_in_graph) {
                    StronglyConnectedComponent scc = (StronglyConnectedComponent) node2scc[node];
                    assert(scc != null);
                    // add the arcs from scc to successor SCCs
                    foreach (object next_node in navigator.NextNodes(node)) 
                        if(nodes_in_graph.Contains(next_node))
                        {
                            StronglyConnectedComponent next = (StronglyConnectedComponent) node2scc[next_node];
                            assert(next != null);
                            scc.next_SCCs.Add(next);
                        }
                    // add the arcs from scc to predecessor SCCs
                    foreach (object prev_node in navigator.PreviousNodes(node))
                        if(nodes_in_graph.Contains(prev_node))
                        {
                            StronglyConnectedComponent prev = (StronglyConnectedComponent) node2scc[prev_node];
                            assert(prev != null);
                            scc.prev_SCCs.Add(prev);
                        }
                }

                foreach (StronglyConnectedComponent scc in all_SCCs) {
                    scc.contains_cycle = scc.next_SCCs.Contains(scc);
                    scc.next_SCCs.Remove(scc);
                    scc.prev_SCCs.Remove(scc);
                }
            }
        }

    }

}

namespace DataStructs
{
    using System;
    using System.Collections;

    /// <summary>
    /// Interface for navigating into a graph.
    /// </summary>
    public interface IGraphNavigator
    {
        /// <summary>
        /// Returns the nodes that can be reached from <c>node</c> by
        /// navigating one level along the graph edges.
        /// </summary>
        IEnumerable! NextNodes (object! node);
        /// <summary>
        /// Returns the nodes that can be reached from <c>node</c> by
        /// navigating one level AGAINST the graph edges (i.e., from edge
        /// target to the edge source).
        /// </summary>
        IEnumerable! PreviousNodes (object! node);
    }


    /// <summary>
    /// Navigator for the graph obtained by unioning two graphs.
    /// </summary>
    public class UnionGraphNavigator: IGraphNavigator
    {
        /// <summary>
        /// Constructs a navigator into a graph which is the union of two graphs
        /// (where the graphs are seen as edge sets).
        /// </summary>
        /// <param name="nav1">Navigator for the first graph.</param>
        /// <param name="nav2">Navigator for the second graph.</param>
        public UnionGraphNavigator(IGraphNavigator! nav1, IGraphNavigator! nav2)
        {
            this.nav1 = nav1;
            this.nav2 = nav2;
        }
        private IGraphNavigator! nav1;
        private IGraphNavigator! nav2;

        /// <summary>
        /// In a union graph, the list of successors of a node includes its successors in
        /// the first graph followed by its successors in the second graph.
        /// </summary>
        public virtual IEnumerable! NextNodes (object! node)
        {
            return new CompoundEnumerable(nav1.NextNodes(node), nav2.NextNodes(node));
        }

        /// <summary>
        /// In a union graph, the list of predecessors of a node includes the its predecessors in
        /// the first graph followed by its predecessors in the second graph.
        /// </summary>
        public virtual IEnumerable! PreviousNodes (object! node)
        {
            return new CompoundEnumerable(nav1.PreviousNodes(node), nav2.PreviousNodes(node));
        }
    }


    public abstract class ForwardOnlyGraphNavigator: IGraphNavigator
    {
        public abstract IEnumerable! NextNodes (object! node);

        public virtual IEnumerable! PreviousNodes (object! node)
        {
            throw new InvalidOperationException("should never be called!");
        }
    }

    /// <summary>
    /// Navigator for an inversed graph.  The successors (i.e., <c>NextNodes</c>)
    /// of a node are the predecessors of the node in the original graph.  Analogously
    /// for the predecessors.
    /// </summary>
    public class BackwardGraphNavigator: IGraphNavigator
    {
        private readonly IGraphNavigator! navigator;

        /// <summary>
        /// Constructs a <c>BackwardGraphNavigator</c> that reverses an
        /// <c>IGraphNavigator</c>.
        /// </summary>
        /// <param name="navigator">The navigator that is reversed.</param>
        public BackwardGraphNavigator(IGraphNavigator! navigator)
        {
            this.navigator = navigator;
            base();
        }

        public IEnumerable! NextNodes (object! node)
        {
            return navigator.PreviousNodes(node);
        }

        public IEnumerable! PreviousNodes (object! node)
        {
            return navigator.NextNodes(node);
        }
    }

    
    public class FilteredGraphNavigator : IGraphNavigator
    {

        IGraphNavigator! graph;
        ISet! nodes;

        /// <summary>
        /// Only nodes in given set are considered part of the graph.
        /// </summary>
        public FilteredGraphNavigator(ISet! nodes, IGraphNavigator! graph) 
        {
            this.graph = graph;
            this.nodes = nodes;
        }

        #region IGraphNavigator Members

        public IEnumerable! NextNodes (object! node)
        {
            return new FilterEnumerable(this.nodes, this.graph.NextNodes(node));
        }

        public IEnumerable! PreviousNodes (object! node)
        {
            return new FilterEnumerable(this.nodes, this.graph.PreviousNodes(node));
        }

        private class FilterEnumerable : IEnumerable
        {
            ISet! nodes;
            IEnumerable! edges;

            public FilterEnumerable(ISet! nodes, IEnumerable! edges) 
            {
                this.nodes = nodes;
                this.edges = edges;
                base();
            }

            public IEnumerator GetEnumerator() { return new FilterEnumerator(this.nodes, this.edges.GetEnumerator()); }


            private class FilterEnumerator : IEnumerator
            {
                ISet! nodes;
                IEnumerator! edges;

                public FilterEnumerator(ISet! nodes, IEnumerator! edges) 
                {
                    this.nodes = nodes;
                    this.edges = edges;
                    base();
                }

                #region IEnumerator Members

                public void Reset()
                {
                    this.edges.Reset();
                }

                public object Current
                {
                    get
                    {
                        return this.edges.Current;
                    }
                }

                public bool MoveNext()
                {
                    while (this.edges.MoveNext()) {
                        if (this.nodes.Contains(this.Current)) {
                            return true;
                        }
                    }
                    return false;
                }

                #endregion

            }
        }
        #endregion
    }


    public class MapBasedNavigator: IGraphNavigator
    {
        protected IMutableRelation! n2next;
        protected IMutableRelation! n2prev;

        public MapBasedNavigator (IMutableRelation! nextRelation, IMutableRelation! previousRelation) 
        {
            n2next = nextRelation; 
            n2prev = previousRelation;
        }

        public MapBasedNavigator (IMutableRelation! nextRelation) 
            : this(nextRelation, nextRelation.Reverse())
        {
        }

        public virtual IEnumerable! NextNodes (object! node)
        {
            return n2next.GetValues(node);
        }

        public virtual IEnumerable! PreviousNodes (object! node)
        {
            return n2prev.GetValues(node);
        }       
    }


    public class GraphBuilder : MapBasedNavigator 
    {
        public GraphBuilder () 
            : base (new Relation(), new Relation())
        {
        }

        public IEnumerable Nodes 
        {
            get 
            { 
                return new UnionEnumerable(n2next.GetKeys(), n2prev.GetKeys()); 
            }
        }

        public void AddEdge(object! from, object! to) 
        {
            this.n2next.Add(from, to);
            this.n2prev.Add(to, from);
        }
    }


    /// <summary>
    /// Navigator in a component graph (an acyclic graph of ISCCs).
    /// </summary>
    public class SccNavigator: IGraphNavigator
    {
        public virtual IEnumerable! NextNodes (object! node)
        {
            return ((IStronglyConnectedComponent) node).NextComponents;
        }

        public virtual IEnumerable! PreviousNodes (object! node)
        {
            return ((IStronglyConnectedComponent) node).PreviousComponents;
        }
    }


    public class CyclicGraphException: Exception { }

    public delegate bool DNodePredicate (Object! node);
    public delegate void DNodeVisitor (Object! node);
    public delegate void DEdgeVisitor (Object! from, Object! to);

    public abstract class GraphUtil
    {
        public static ISet! ReachableNodes (IEnumerable! roots, IGraphNavigator! navigator,  DNodePredicate avoid)
        {
            ReachableNodesData data = new ReachableNodesData();
            SearchDepthFirst(roots, navigator, avoid, null,
                new DNodeVisitor(data.reachable_visitor), null);
            return data.all_nodes;
        }

        private class ReachableNodesData
        {
            public IMutableSet! all_nodes  = new HashSet();
            public void reachable_visitor(object! node)
            {
                all_nodes.Add(node);
            }
        }

        public static ISet! ReachableNodes (IEnumerable! roots, IGraphNavigator! navigator) 
        {
            return ReachableNodes(roots, navigator, null);
        }


        /// <summary>
        /// Topologically sorts the graph rooted in <c>roots</c> and described by
        /// <c>nav</c>. Throws a <c>CyclicGraphException</c> if the graph contains
        /// a cycle. Otherwise, returns a topologically sorted list of the graph nodes. 
        /// The returned list is in ascending order: it starts with the nodes that don't
        /// have any out-arc (i.e., arcs going out of them) and ends with the nodes
        /// that don't have any in-arcs (i.e., arcs going into them).  If the navigator
        /// works in constant time, the topological sort works in time linear with the
        /// number of nodes plus the number of edges. 
        /// 
        /// </summary>
        public static IList TopologicallySortGraph (IEnumerable! roots, IGraphNavigator! navigator)
        {
            TopSortData data = new TopSortData();
            data.all_nodes.AddAll(ReachableNodes(roots, navigator));
            if (data.all_nodes.Count == 0)
                return data.list;

            // find the real roots: those nodes with no arcs pointing to them
            data.real_roots.AddAll(roots);
            foreach (object node in data.all_nodes)
                foreach(object next_node in navigator.NextNodes(node))
                    data.real_roots.Remove(next_node);
            // if there is no real root, we have a cycle
            if (data.real_roots.Count == 0)
                throw new CyclicGraphException();

            dfs(data.real_roots, navigator, null, null,
                new DNodeVisitor(data.sort_end_visitor));

#if NEVER
            // check for cyles
            IMutableSet seen = new HashSet();
            foreach (object node in data.list) {
                foreach (object next_node in navigator.NextNodes(node))
                    // all arcs must go behind in the list, to already seen nodes
                    if (!seen.Contains(next_node))
                        throw new CyclicGraphException();
                seen.Add(node);
            }
#endif
            return data.list;
        }

        private class TopSortData
        {
            public ArrayList! list  = new ArrayList();
            public IMutableSet! all_nodes  = new HashSet();
            public IMutableSet! real_roots = new HashSet();
            public void sort_end_visitor(object! node)
            {
                list.Add(node);
            }
        }


        /// <summary>
        /// Topologically sorts a component graph: a graph whose nodes are the
        /// strongly connected components of the original graph (such a graph is
        /// clearly acyclic). Calls the full-fledged TopSortComponentGraph with
        /// the standard <c>ISCCNavigator</c>.
        /// 
        /// </summary>
        /// <param name="roots">The set of the root SCCs, only the SCCs reacheable
        /// from these roots will be considered by the topological sort.</param>
        /// <returns></returns>
        public static IList//<IStronglyConnectedComponent>   
            TopologicallySortComponentGraph(IEnumerable!/*<IStronglyConnectedComponent>*/ roots)
        {
            return TopologicallySortGraph(roots, iscc_navigator);
        }
        // private navigator for TopSortComponentGraph
        private static SccNavigator! iscc_navigator = new SccNavigator();

        /// <summary>
        /// DFS traversal of the (sub)graph rooted in a set of nodes.
        /// </summary>
        /// <param name="roots">Roots of the traversed subgraph. The subgraph
        /// rooted in the first root will be traversed in dfs order; next, if
        /// the second root wasn't reached yet, the subgraph rooted in it will
        /// be traversed in dfs order and so on. The order of
        /// the roots is given by the corresponding <c>IEnumerator</c>.</param>
        /// <param name="navigator">Navigator that describes the graph structure.</param>
        /// <param name="avoid">Encountered nodes that satisfy this predicate will be
        /// ignored by the DFS traversal (together with their attached arcs). <c>null</c>
        /// corresponds to the predicate that is always false (i.e., no encountered node
        /// will be ignored).</param>
        /// <param name="new_subgraph_visitor">Visitor for the root node of each
        /// new subgraph: the roots (see the <see cref="roots">roots</see> parameter)
        /// are explored in order; if a root node has not been already reached
        /// by the dfs traversal of the previous roots, <c>new_subgraph_visitor</c>
        /// will be called on it, and next the subgraph rooted in it will be dfs
        /// traversed.</param>
        /// <param name="begin_visitor">Node visitor to be called when a node is reached
        /// for the first time by the DFS traversal. <c>null</c> corresponds to no
        /// visitor.</param>
        /// <param name="end_visitor">Node visitor to be called when the exploration of
        /// a node has finished. <c>null</c> corresponds to no visitor.</param>
        public static void SearchDepthFirst (
            IEnumerable! roots, 
            IGraphNavigator! navigator,
             DNodePredicate avoid,
             DNodeVisitor new_subgraph_visitor,
             DNodeVisitor begin_visitor,
             DNodeVisitor end_visitor
            )
        {
            // set of already seen nodes
            IMutableSet seen_nodes = new HashSet();
            // DFS Stack: holds the currently explored path; simulates the call
            // stack of a recursive implementation of dfs.
            Stack/*<NodeInfo>*/ stack = new Stack();

            foreach (object root in roots) {
                if (((avoid != null) && avoid(root)) ||
                    seen_nodes.Contains(root)) continue;

                call_visitor(new_subgraph_visitor, root);

                seen_nodes.Add(root);
                call_visitor(begin_visitor, root);
                stack.Push(new NodeInfo(root, navigator));
                while (stack.Count != 0) {
                    NodeInfo info = (NodeInfo) (object!)stack.Peek();
                    if (info.enext.MoveNext()) {
                        object next_node = info.enext.Current;
                        // ignore nodes as dictated by "avoid"
                        if ((avoid != null) && avoid(next_node))
                            continue;
                        
                        if (!seen_nodes.Contains(next_node)) {
                            // new and non-avoidable node!
                            // mark it as seen,
                            seen_nodes.Add(next_node);
                            // call the begin visitor,
                            call_visitor(begin_visitor, next_node);
                            // and put the node on the DFS stack
                            stack.Push(new NodeInfo(next_node, navigator));
                        }
                    }
                    else {
                        // the visit of info.node has finished
                        // apply end visitor
                        call_visitor(end_visitor, info.node);
                        // remove the top of the stack
                        stack.Pop();
                    }
                }
            }
        }


        /// <summary>
        /// Convenient <c>dfs</c> function.  Call the full <c>dfs</c> function
        /// with new_subgraph_visitor set to <c>null</c>.
        /// </summary>
        public static void dfs (
            IEnumerable! roots, 
            IGraphNavigator! navigator,
             DNodePredicate avoid,
             DNodeVisitor begin_visitor,
             DNodeVisitor end_visitor)
        {
            SearchDepthFirst(roots, navigator, avoid, null, begin_visitor, end_visitor);
        }

        private static void call_visitor(  DNodeVisitor visitor, object! node)
        {
            if (visitor != null)
                visitor(node);
        }

        // private class used internally by the dfs method.
        private struct NodeInfo
        {
            public object! node;
            public IEnumerator! enext ;
            public NodeInfo(object! node, IGraphNavigator! navigator)
            {
                this.node  = node;
                this.enext = navigator.NextNodes(node).GetEnumerator();
            }
        }



        /// <summary>
        /// Does a breadth first traversal of the given graph
        /// </summary>
        /// <param name="roots">The roots of the traversal.</param>
        /// <param name="avoid">If not null, is a predicate to avoid certain nodes</param>
        /// <param name="visitRoot">If not null, called for each root that is not avoided.</param>
        /// <param name="visitEdge">Called for each edges in the bf traversal, i.e., only for edges going to unvisited nodes.</param>
        public static void bfs(IEnumerable! roots, IGraphNavigator! navigator,
             DNodePredicate avoid,
             DNodeVisitor visitRoot,
             DEdgeVisitor! visitEdge)
        {
            Queue queue = new Queue();
            IMutableSet seen = new HashSet();

            // initialize queue with roots
            foreach (object o in roots) {
                if (avoid == null || !avoid(o)) {
                    queue.Enqueue(o);
                    seen.Add(o);
                    if (visitRoot != null) visitRoot(o);
                }
            }

            while (queue.Count > 0) {
                object node = queue.Dequeue();
                assert(node != null);
                foreach (object succ in navigator.NextNodes(node)) {
                    if ((avoid == null || !avoid(succ)) && !seen.Contains(succ)) {
                        seen.Add(succ);
                        queue.Enqueue(succ);
                        visitEdge(node, succ);
                    }
                }
            }
        }




        private class BFSpanningBuilder : MapBasedNavigator
        {
            public BFSpanningBuilder () 
                : base (new Relation(), new Relation())
            {
            }

            public void VisitEdge(object! from, object! to) 
            {
                this.n2next.Add(from, to);
                this.n2prev.Add(to, from);
            }
        }

        public static IGraphNavigator BFSpanningTree(IEnumerable! roots, IGraphNavigator! navigator, 
             DNodePredicate avoid) 
        {
            BFSpanningBuilder bfb = new BFSpanningBuilder();

            bfs(roots, navigator, avoid, null, new DEdgeVisitor(bfb.VisitEdge));

            return bfb;
        }
    }

}


namespace DataStructs
{
    using System;
    using System.Collections;


    public class ArrayEnumerable : IEnumerable
    {
        object[]! array;
        int size;

        public ArrayEnumerable(object[]! array, int size) 
        {
            this.array = array;
            this.size = size;
        }

        #region IEnumerable Members

        public IEnumerator GetEnumerator()
        {
            return new ArrayEnumerator(this.array, this.size);
        }

        #endregion

    }



    /// <summary>
    /// Enumerator over a prefix of an array (System.Array.GetEnumerator returns
    /// an enumerator over ALL the elements of the array).
    /// </summary>
    public class ArrayEnumerator : IEnumerator
    {
        /// <summary>
        /// Constructs an enumerator  over the first <c>size</c> elements of <c>array</c>.
        /// NOTE: I couldn't find any way of detecting comodification errors ...
        /// </summary>
        public ArrayEnumerator(object[]! array, int size)
        {
            this.array = array;
            this.size  = size;
            this.index = -1;
        }

        // underlying array
        private readonly object[]! array;
        // length of the prefix of array that we enumerate over
        private readonly int      size;
        // current enumerator position
        private int index;


        public virtual object Current
        {
            get 
            {
                if ((index >= 0) && (index < size)) return array[index];
                else
                    throw new InvalidOperationException();
            }
        }


        public virtual bool MoveNext()
        {
            if (index == size)
                return false;
            index++;
            // check whether we've passed the limit or not
            return index != size;
        }


        public virtual void Reset()
        {
            index = -1;
        }
    }
}


namespace DataStructs 
{
    using System;
    using System.Collections;


    /// <summary>
    /// Union enumerator over two <c>IEnumerable</c> objects. Each key is visited only once
    /// </summary>
    public class UnionEnumerable: IEnumerable 
    {

        public UnionEnumerable(IEnumerable! ieable1, IEnumerable! ieable2) 
            : this(new IEnumerable[]{ieable1, ieable2})
        {
        }

        public UnionEnumerable(IEnumerable!/*<IEnumerable>*/ ienums) 
        {
            this.ienums = ienums;
        }

        private IEnumerable!/*<IEnumerable>*/ ienums;

        public virtual IEnumerator GetEnumerator() 
        {
            return new UnionEnumerator(ienums);
        }
    }

    /// <summary>
    /// Union composition of two enumerators.  Enumerating with a
    /// multi-enumerator is equivalent to enumerating over the union of the elements in
    /// the first and second enumerator.
    /// </summary>
    public class UnionEnumerator: IEnumerator 
    {
        /// <summary>
        /// Creates a <c>UnionEnumerator</c> over both given enumerators.
        /// </summary>
        public UnionEnumerator(IEnumerable!/*<IEnumerable>*/ ienums) 
        {
            this.ies = ienums;

            // Duplicate from Reset 
            IEnumerator ienum = this.ienumate = ienums.GetEnumerator();
            // go to first enumerator.
            MoveEnumerator(ienum);
        }

        public void Reset() 
        {
            seen.Clear();

            IEnumerator ienum = this.ienumate = ies.GetEnumerator();
            // go to first enumerator.
            MoveEnumerator(ienum);
        }

        [Delayed]
        private void MoveEnumerator(IEnumerator! ienum) 
        {
            if (ienum.MoveNext()) {
                this.current_ie = ((IEnumerable)ienum.Current).GetEnumerator();
            }
            else {
                this.current_ie = null;
            }
        }


        public UnionEnumerator(IEnumerable ie1, IEnumerable ie2) : this(new IEnumerable[]{ie1,ie2})
        {
        }

        private HashSet! seen = new HashSet();
        private IEnumerable!/*<IEnumerable>*/ ies;
        private IEnumerator!/*<IEnumerable>*/ ienumate;
        private IEnumerator/*<'a>*/ current_ie;

        public virtual object Current 
        {
            get 
            {
                if (current_ie == null)
                    throw new InvalidOperationException("exhausted enumerator");
                return
                    current_ie.Current;
            }
        }

        public virtual bool MoveNext() 
        {
            while (current_ie != null) {
                if (current_ie.MoveNext()) {
                    if (this.seen.Add(current_ie.Current)) {
                        return true;
                    }
                    // already seen
                    continue;
                }
                // move to next ienumerable
                MoveEnumerator(this.ienumate);
            }
            return false;
        }

    }
}

namespace DataStructs 
{
    using System;
    using System.Collections;


    /// <summary>
    /// Returns null if object should not be returned, otherwise, returns object.
    /// Can thus change objects.
    /// </summary>
    public delegate object EnumeratorFilter(object elem, object context);

    /// <summary>
    /// "Glues" together two <c>IEnumerable</c> objects in a single view.
    /// </summary>
    public class CompoundEnumerable: IEnumerable 
    {

        /// <summary>
        /// Construct an enumerable that enumerators over ieable1, then ieable2. Each element
        /// is passed to the filter which can decide if the element should be returned by
        /// the enumerator or not. The filter can also change the element (map).
        /// </summary>
        /// <param name="filter">can be null</param>
        /// <param name="context">passed to filter</param>
        public CompoundEnumerable (
            IEnumerable! ieable1,
            IEnumerable! ieable2,
            EnumeratorFilter filter, 
            object context) 
        {
            this.ieable1 = ieable1;
            this.ieable2 = ieable2;
            this.filter = filter;
            this.context = context;
        }

        public CompoundEnumerable(IEnumerable! ieable1, IEnumerable! ieable2) : this(ieable1, ieable2, null, null)
        {
        }

        private IEnumerable! ieable1;
        private IEnumerable! ieable2;
        private EnumeratorFilter filter;
        private object context;

        public virtual IEnumerator GetEnumerator() 
        {
            return 
                new MultiEnumerator(ieable1.GetEnumerator(), ieable2.GetEnumerator(), filter, context);
        }
    }

    /// <summary>
    /// Serial composition of two enumerators.  Enumerating with a
    /// multi-enumerator is equivalent to enumerating with the first enumerator,
    /// and next with the second one.  Implements the full <c>IEnumerable</c>
    /// interface.  Aliases to the enumerators are sequentially composed are
    /// internally stored and used by the encapsulating multi-enumerator.
    /// </summary>
    public class MultiEnumerator: IEnumerator 
    {
        /// <summary>
        /// Creates a <c>MultiEnumerator</c> that serially chains the two
        /// enumerators passed as arguments.
        /// </summary>
        [NotDelayed]
        public MultiEnumerator(IEnumerator! ie1, IEnumerator! ie2,  EnumeratorFilter filter, object context) 
        {
            this.filter = filter;
            this.context = context;
            ies = new IEnumerator[]{ie1, ie2};
            base();
            ((IEnumerator!)ies[0]).Reset();
            ((IEnumerator!)ies[1]).Reset();
        }

        
        private EnumeratorFilter filter;
        private IEnumerator[]! ies;
        private int current_ie;
        private object context;

        private object currentValue;

        public virtual object Current 
        {
            get 
            {
                if (current_ie >= ies.Length)
                    throw new InvalidOperationException("exhausted enumerator");
                return
                    this.currentValue;
            }
        }

        public virtual bool MoveNext() 
        {
            if (current_ie >= ies.Length)
                return false;
            while (current_ie < ies.Length) {
                if (((IEnumerator!)ies[current_ie]).MoveNext()) {
                    object value = ((IEnumerator!)ies[current_ie]).Current;
                    if (this.filter != null) {
                        value = filter(value, this.context);
                        if (value == null) // skip this one
                        {
                            continue;
                        }
                    }
                    this.currentValue = value;
                    return true;
                }
                ((IEnumerator!)ies[current_ie]).Reset();
                current_ie++;                
            }
            return false;
        }

        public virtual void Reset() 
        {
            if (current_ie < ies.Length)
                ((IEnumerator!)ies[current_ie]).Reset();
            current_ie = 0;
        }
    }
}

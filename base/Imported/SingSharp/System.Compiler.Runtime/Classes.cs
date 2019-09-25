using System;

#if WHIDBEYwithGenerics
#if CCINamespace
namespace Microsoft.Cci{
#else
namespace System.Compiler{
#endif
  /// <summary>
  /// Tells a sympathetic compiler that the name of the entity bearing this attribute should be suppressed. When applied to a class or enum,
  /// this means that the members of the class or enum should be injected into the same scope as would have contained the class/enum name.
  /// When applied to a field or property, it means that the members of structure of the type of the field/property should be visible
  /// without qualification by the field/property name.
  /// </summary>
  [AttributeUsage(AttributeTargets.Field|AttributeTargets.Property|AttributeTargets.Class|AttributeTargets.Enum)]
  public sealed class AnonymousAttribute: Attribute{
    private Anonymity type;
    public AnonymousAttribute(){
      this.type = Anonymity.Structural;
    }
    public Anonymity Anonymity{
      get {return this.type;}
    }
  }  
  public enum Anonymity{
    Unknown,
    None,
    Structural,
    Full
  }
  public enum CciMemberKind {
    Unknown,
    Regular,
    Auxiliary,
    FrameGuardGetter,
  }
  [AttributeUsage(AttributeTargets.All)]
  public class CciMemberKindAttribute : Attribute {
    public CciMemberKind Kind;
    public CciMemberKindAttribute(CciMemberKind kind) {
      this.Kind = kind;
    }
  }
  [AttributeUsage(AttributeTargets.Class)]
  public sealed class ComposerAttribute: Attribute{
    public string AssemblyName = null;
    public string TypeName = null;
    public ComposerAttribute(){
    }
  }
  [AttributeUsage(AttributeTargets.Assembly|AttributeTargets.Module, AllowMultiple=true)]
  public sealed class CustomVisitorAttribute : Attribute{
    public string Assembly;
    public string Class;
    public string Phase;
    public bool Replace;
    public CustomVisitorAttribute(){
    }
  }
  [AttributeUsage(AttributeTargets.Class|AttributeTargets.Field|AttributeTargets.Property|AttributeTargets.Method)]
  public sealed class ElementTypeAttribute: Attribute{
    public Type ElementType = null;
    public ElementTypeAttribute(){
    }
  }  
  public interface ITemplateParameter{
  }
  [AttributeUsage(AttributeTargets.Interface|AttributeTargets.Class|AttributeTargets.Struct)]
  public sealed class TemplateAttribute : System.Attribute{
    public Type[] TemplateParameters;
    public TemplateAttribute(params Type[] parameters){
      this.TemplateParameters = parameters;
    }
  }
  [AttributeUsage(AttributeTargets.Interface|AttributeTargets.Class|AttributeTargets.Delegate|AttributeTargets.Interface|AttributeTargets.Struct)]
  public sealed class TemplateInstanceAttribute : System.Attribute{
    public Type Template;
    public Type[] TemplateArguments;
    public TemplateInstanceAttribute(Type template, params Type[] arguments){
      this.Template = template;
    }
  }
  [AttributeUsage(AttributeTargets.Class | AttributeTargets.Interface | AttributeTargets.Struct)]
  public sealed class TemplateParameterFlagsAttribute : System.Attribute {
    public int Flags;
    public TemplateParameterFlagsAttribute(int flags) {
      this.Flags = flags;
    }
  }

  namespace Diagnostics{
    public sealed class Debug{
      public static void Assert(bool condition){
        System.Diagnostics.Debug.Assert(condition);
      }
    }
  }
}
#if !NoData
namespace System.Data{
  public interface IDbTransactable{ //TODO: move to Query namespace
    IDbTransaction BeginTransaction();
    IDbTransaction BeginTransaction(IsolationLevel level);
  }
}
#endif
namespace StructuralTypes{
#if CCINamespace
  using Microsoft.Cci;
#else
  using System.Compiler;
#endif
  using System.Collections;
  using System.Collections.Generic;
  using SCIEnumerator = System.Collections.IEnumerator;
 
  public interface IConstrainedType{}
  public interface ITupleType{}
  public interface ITypeUnion{}
  public interface ITypeIntersection{}
  public interface ITypeAlias{}
  public interface ITypeDefinition{}

  public struct Boxed<ElementType> : IEnumerable<ElementType>, IEnumerable{
    private ElementType[] box;
    public Boxed(ElementType value){
      this.box = new ElementType[]{value};
    }
    public ElementType GetValue(){
      return this.box[0];
    }
    public void SetValue(ElementType value){
      this.box[0] = value;
    }
    public object ToObject(){
      if (this.box == null) return null;
      return this.box[0];
    }
    public bool IsNull(){
      return this.box == null;
    }
    IEnumerator IEnumerable.GetEnumerator() {
      return new BoxedEnumerator<ElementType>(this.box);
    }
    IEnumerator<ElementType> IEnumerable<ElementType>.GetEnumerator(){
      return new BoxedEnumerator<ElementType>(this.box);
    }
    public BoxedEnumerator<ElementType> GetEnumerator(){
      return new BoxedEnumerator<ElementType>(this.box);
    }
    public void Clear(){
      this.box = null;
    }
    public static implicit operator Boxed<ElementType>(ElementType value){
      return new Boxed<ElementType>(value);
    }
    public static explicit operator ElementType(Boxed<ElementType> boxed){
      return boxed.GetValue();
    }
    public static bool operator == (Boxed<ElementType> a, Boxed<ElementType> b){
      if (a.box == null || b.box == null) return false;
      return a.box[0].Equals(b.box[0]);
    }
    public static bool operator == (Boxed<ElementType> a, object o){
      return a.Equals(o);
    }
    public static bool operator != (Boxed<ElementType> a, object o){
      return !a.Equals(o);
    }
    public static bool operator == (object o, Boxed<ElementType> b){
      return b.Equals(o);
    }
    public static bool operator != (object o, Boxed<ElementType> b){
      return !b.Equals(o);
    }
    public static bool operator != (Boxed<ElementType> a, Boxed<ElementType> b){
      if (a.box == null || b.box == null) return false;
      return !a.box[0].Equals(b.box[0]);
    }
    public override bool Equals(object o){
      if (this.box == null) return o == null;
      if (!(o is Boxed<ElementType>)) return false;
      Boxed<ElementType> b = (Boxed<ElementType>) o;
      if (this.box == null || b.box == null) return this.box == b.box;
      return this.box[0].Equals(b.box[0]);
 
    }
    public override int GetHashCode(){
      return this.box[0].GetHashCode();
    }
  }
  public struct BoxedEnumerator<ElementType>: IEnumerator<ElementType>, IEnumerator{
    private ElementType[] box;
    private int index;
    internal BoxedEnumerator(ElementType[] box){
      this.box = box;
      this.index = -1;
    }
    object IEnumerator.Current{
      get{
        return this.box[0];
      }
    }
    public ElementType Current{
      get{ 
        return this.box[0];
      }
    }
    void IEnumerator.Reset() {
      this.index = -1;
    }
    void IDisposable.Dispose(){
    }
    public bool MoveNext(){
      if (this.box == null) return false;
      return ++this.index == 0;
    }
  }
  public struct Invariant<ElementType>{
    private ElementType value;
    public Invariant(ElementType value){
      if (value == null) throw new ArgumentNullException();
      if (value.GetType() != typeof(ElementType)) throw new ArgumentException();
      this.value = value;
    }
    public ElementType GetValue(){
      return this.value;
    }
    public object ToObject(){
      return this.value;
    }
    public static implicit operator ElementType(Invariant<ElementType> invariantValue){
      return invariantValue.value;
    }
    public static implicit operator NonNull<ElementType>(Invariant<ElementType> invariantValue){
      return new NonNull<ElementType>(invariantValue.value);
    }
    public static explicit operator Invariant<ElementType>(ElementType value){
      return new Invariant<ElementType>(value);
    }
  }
  public struct NonNull<ElementType>: IEnumerable<ElementType>, IEnumerable{
    private ElementType value;
    public NonNull(ElementType value){
      if (value == null) throw new ArgumentNullException();
      this.value = value;
    }
    public ElementType GetValue(){
      return this.value;
    }
    public object ToObject(){
      return this.value;
    }
    IEnumerator IEnumerable.GetEnumerator(){
        return new ValueEnumerator<ElementType>(this.value);
    }
    IEnumerator<ElementType> IEnumerable<ElementType>.GetEnumerator(){
      return new ValueEnumerator<ElementType>(this.value);
    }
    public ValueEnumerator<ElementType> GetEnumerator(){
      return new ValueEnumerator<ElementType>(this.value);
    }
    public static implicit operator ElementType(NonNull<ElementType> nonNullValue){
      return nonNullValue.value;
    }
    public static explicit operator NonNull<ElementType>(ElementType value){
      return new NonNull<ElementType>(value);
    }
  }
  public struct NonEmptyIEnumerable<ElementType>: IEnumerable<ElementType>, IEnumerable{
    IEnumerable<ElementType> enumerable;
    public NonEmptyIEnumerable(IEnumerable<ElementType> enumerable){
      this.enumerable = enumerable;
      if (enumerable == null) 
        throw new ArgumentNullException();
      if (!(enumerable is IEnumerable))
        throw new ArgumentException();
      IEnumerator<ElementType> enumerator = enumerable.GetEnumerator();
      if (enumerator == null || !enumerator.MoveNext())
        throw new ArgumentException();
    }
    public NonEmptyIEnumerable(ElementType element){
      this.enumerable = new NonNull<ElementType>(element);
    }
    public ElementType GetValue(){
      IEnumerator<ElementType> e = this.enumerable.GetEnumerator();
      if (e.MoveNext()){
        ElementType result = e.Current;
        if (!e.MoveNext()) return result;
      }
      throw new ArgumentOutOfRangeException();
    }
    public object ToObject(){
      if (this.enumerable is NonNull<ElementType>){
        NonNull<ElementType> nnull = (NonNull<ElementType>)this.enumerable;
        return nnull.ToObject();
      }
      if (this.enumerable is Boxed<ElementType>){
        Boxed<ElementType> boxed = (Boxed<ElementType>)this.enumerable;
        return boxed.ToObject();
      }
      return this.enumerable;
    }
    IEnumerator IEnumerable.GetEnumerator() {
        return ((IEnumerable)this.enumerable).GetEnumerator();
    }
    public IEnumerator<ElementType> GetEnumerator(){
      return this.enumerable.GetEnumerator();
    }
    public static implicit operator NonEmptyIEnumerable<ElementType>(NonNull<ElementType> element){
      return new NonEmptyIEnumerable<ElementType>((IEnumerable<ElementType>)element);
    }
    public static explicit operator NonEmptyIEnumerable<ElementType>(ElementType element){
      return new NonEmptyIEnumerable<ElementType>(element);
    }
    public static explicit operator NonEmptyIEnumerable<ElementType>(Boxed<ElementType> element){
      return new NonEmptyIEnumerable<ElementType>((IEnumerable<ElementType>)element);
    }
    public static explicit operator NonEmptyIEnumerable<ElementType>(ElementType[] array){
      return new NonEmptyIEnumerable<ElementType>(array);
    }
    public static explicit operator NonEmptyIEnumerable<ElementType>(List<ElementType> list){
      return new NonEmptyIEnumerable<ElementType>(list);
    }
    public static explicit operator ElementType(NonEmptyIEnumerable<ElementType> nonEmptyIEnumerable){
      return nonEmptyIEnumerable.GetValue();
    }
  }
  public sealed class Unboxer<ElementType>{
    public static object ToObject(IEnumerable<ElementType> collection){
      if (collection is NonNull<ElementType>)
        return ((NonNull<ElementType>)collection).ToObject();
      if (collection is Boxed<ElementType>)
        return ((Boxed<ElementType>)collection).ToObject();
      return collection;
    }
  }
  public struct ArrayEnumerator<ElementType>: IEnumerator<ElementType>, SCIEnumerator{
    private ElementType[] array;
    private int index;
    public ArrayEnumerator(ElementType[] array){
      this.array = array;
      this.index = -1;
    }
    public ElementType Current{
      get{
        return this.array[this.index];
      }
    }
    object SCIEnumerator.Current{
      get{
        return this.array[this.index];
      }
    }
    void IDisposable.Dispose(){
    }
    public bool MoveNext(){
      return ++this.index < this.array.Length;
    }
    void SCIEnumerator.Reset(){
      this.index = -1;
    }
  }
  public sealed class GenericIEnumerableToGenericIListAdapter<ElementType>: IList<ElementType>, IEnumerable{
    private List<ElementType> list;
    private IEnumerable<ElementType> collection;
    public GenericIEnumerableToGenericIListAdapter(IEnumerable<ElementType> collection){
      if (collection == null) 
        throw new ArgumentNullException();
      if (!(collection is IEnumerable))
        throw new ArgumentException();
      this.collection = collection;
    }

    private List<ElementType>/*!*/ List{
      get{
        List<ElementType> result = this.list;
        if (result == null){
          result = new List<ElementType>();
          this.list = result;
          if (this.collection != null){
            IEnumerator<ElementType> enumerator = this.collection.GetEnumerator();
            if (enumerator != null){
              while (enumerator.MoveNext()){
                //result.Add(enumerator.Current);
                ElementType curr = enumerator.Current;
                result.Add(curr);
              }
            }
          }
        }
        return result;
      }
    }
    IEnumerator IEnumerable.GetEnumerator() {
      if (this.list != null)
        return this.list.GetEnumerator();
      else
        return ((IEnumerable)this.collection).GetEnumerator();
    }
    public IEnumerator<ElementType> GetEnumerator(){
      if (this.list != null)
        return this.list.GetEnumerator();
      else
        return this.collection.GetEnumerator();
    }
    public int Count{
      get{
        return this.List.Count;
      }
    }
    public bool IsSynchronized{
      get{
        return false;
      }
    }
    public object SyncRoot{
      get{
        return this;
      }
    }
    void ICollection<ElementType>.CopyTo(ElementType[] array, int index){
      this.List.CopyTo(array, index);
    }

    public bool IsFixedSize{
      get{
        return false;
      }
    }
    public bool IsReadOnly{
      get{
        return false;
      }
    }
    public ElementType this[int index]{
      get{
        return this.List[index];
      }
      set{
        this.List[index] = value;
      }
    }
    public void Add(ElementType value){
      this.List.Add(value);
    }
    public void Clear(){
      this.List.Clear();
    }
    public bool Contains(ElementType value){
      return this.List.Contains(value);
    }
    public int IndexOf(ElementType value){
      return this.List.IndexOf(value);
    }
    public void Insert(int index, ElementType value){
      this.List.Insert(index, value);
    }    
    public bool Remove(ElementType value){
      return this.List.Remove(value);
    }
    public void RemoveAt(int index){
      this.List.RemoveAt(index);
    }
  }
  public struct ValueEnumerator<ElementType>: IEnumerator<ElementType>, IEnumerator{
    private ElementType value;
    private int index;

    public ValueEnumerator(ElementType value){
      this.value = value;
      this.index = -1;
    }

    object IEnumerator.Current{
        get{
            return this.value;
        }
    }
    public ElementType Current{
      get{
        return this.value;
      }
    }
    void IEnumerator.Reset(){
        this.index = -1;
    }
    void IDisposable.Dispose(){
    }
    public bool MoveNext(){
      return ++this.index == 0;
    }
  }

  public sealed class StreamUtility<ElementType>{
    private StreamUtility(){}
    public static bool IsNull(IEnumerable<ElementType> stream){
      if (stream == null) return true;
      IEnumerator<ElementType> enumerator = stream.GetEnumerator();
      while (enumerator.MoveNext())
        if (enumerator.Current != null) return false;
      return true;
    }
  }
}
#if !NoData
namespace System.Query{ //TODO: rename to Microsoft.Cci.Query
#if CCINamespace
  using Microsoft.Cci;
#else
  using System.Compiler;
#endif
  using System.Collections.Generic;
  using System.Data.SqlTypes;
  using System.Text;

  //TODO: this class should derive from SystemException and it should not contain a string
  //The message, if any, should be obtained from a resource file
  public class StreamNotSingletonException: Exception{
    public StreamNotSingletonException(): base("Stream not singleton"){
    }
  }
  
  public interface IAggregate{
  }
  public interface IAggregateGroup{
  }

  public class Min: IAggregateGroup{
    public struct MinOfByte: IAggregate{
      byte value;
      bool hasValue;
      public void Add(byte value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value){
          this.value = value;
        }
      }
      public byte GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfInt16: IAggregate{
      short value;
      bool hasValue;
      public void Add(short value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value){
          this.value = value;
        }
      }
      public short GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfInt32: IAggregate{
      int value;
      bool hasValue;
      public void Add(int value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value){
          this.value = value;
        }
      }
      public int GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfInt64: IAggregate{
      long value;
      bool hasValue;
      public void Add(long value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value)
          this.value = value;
      }
      public long GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfSingle: IAggregate{
      float value;
      bool hasValue;
      public void Add(float value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value){
          this.value = value;
        }
      }
      public float GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfDouble: IAggregate{
      double value;
      bool hasValue;
      public void Add(double value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value)
          this.value = value;
      }
      public double GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfDecimal: IAggregate{
      decimal value;
      bool hasValue;
      public void Add(decimal value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value)
          this.value = value;
      }
      public decimal GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfString: IAggregate{
      string value;
      public void Add(string value){
        if (value != null){
          if (this.value == null || value.CompareTo(this.value) < 0)
            this.value = value;
        }
      }
      public string GetValue(){
        string result = this.value;
        this.value = null;
        return result;
      }
    }
    public struct MinOfDateTime: IAggregate{
      DateTime value;
      bool hasValue;
      public void Add(DateTime value){
        if (!this.hasValue || value < this.value){
          this.value = value;
          this.hasValue = true;
        }
      }
      public DateTime GetValue(){
        DateTime result = this.value;
        this.value = new DateTime();
        this.hasValue = false;
        return result;
      }
    }
    public struct MinOfSqlByte: IAggregate{
      byte value;
      bool hasValue;
      public void Add(SqlByte value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (byte)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (byte)value;
          }
        }
      }
      public SqlByte GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlByte.Null;
      }
    }
    public struct MinOfSqlInt16: IAggregate{
      short value;
      bool hasValue;
      public void Add(SqlInt16 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (short)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (short)value;
          }
        }
      }
      public SqlInt16 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt16.Null;
      }
    }
    public struct MinOfSqlInt32: IAggregate{
      int value;
      bool hasValue;
      public void Add(SqlInt32 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (int)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (int)value;
          }
        }
      }
      public SqlInt32 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt32.Null;
      }
    }
    public struct MinOfSqlInt64: IAggregate{
      long value;
      bool hasValue;
      public void Add(SqlInt64 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (long)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (long)value;
          }
        }
      }
      public SqlInt64 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt64.Null;
      }
    }
    public struct MinOfSqlSingle: IAggregate{
      float value;
      bool hasValue;
      public void Add(SqlSingle value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value.Value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = value.Value;
          }
        }
      }
      public SqlSingle GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlSingle.Null;
      }
    }
    public struct MinOfSqlDouble: IAggregate{
      double value;
      bool hasValue;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (double)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (double)value;
          }
        }
      }
      public SqlDouble GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDouble.Null;
      }
    }
    public struct MinOfSqlDecimal: IAggregate{
      SqlDecimal value;
      bool hasValue;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = value;
          }
        }
      }
      public SqlDecimal GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDecimal.Null;
      }
    }
    public struct MinOfSqlMoney: IAggregate{
      SqlMoney value;
      bool hasValue;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = value;
          }
        }
      }
      public SqlMoney GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlMoney.Null;
      }
    }
    public struct MinOfSqlString: IAggregate{
      SqlString value;
      bool hasValue;
      public void Add(SqlString value){
        if (!value.IsNull){
          if (!this.hasValue || (bool)SqlString.LessThan(value, this.value)){
            this.value = value;
            this.hasValue = true;
          }
        }
      }
      public SqlString GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlString.Null;
      }
    }
    public struct MinOfSqlDateTime: IAggregate{
      SqlDateTime value;
      bool hasValue;
      public void Add(SqlDateTime value){
        if (!value.IsNull){
          if (!this.hasValue || (bool)SqlDateTime.LessThan(value, this.value)){
            this.value = value;
            this.hasValue = true;
          }
        }
      }
      public SqlDateTime GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDateTime.Null;
      }
    }
  }
  public class Max: IAggregateGroup{
    public struct MaxOfByte: IAggregate{
      byte value;
      bool hasValue;
      public void Add(byte value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public byte GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfInt16: IAggregate{
      short value;
      bool hasValue;
      public void Add(short value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public short GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfInt32: IAggregate{
      int value;
      bool hasValue;
      public void Add(int value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public int GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfInt64: IAggregate{
      long value;
      bool hasValue;
      public void Add(long value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public long GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfSingle: IAggregate{
      float value;
      bool hasValue;
      public void Add(float value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public float GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfDouble: IAggregate{
      double value;
      bool hasValue;
      public void Add(double value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public double GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfDecimal: IAggregate{
      decimal value;
      bool hasValue;
      public void Add(decimal value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public decimal GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfString: IAggregate{
      string value;
      public void Add(string value){
        if (value != null){
          if (this.value == null || value.CompareTo(this.value) > 0)
            this.value = value;
        }
      }
      public string GetValue(){
        string result = this.value;
        this.value = null;
        return result;
      }
    }
    public struct MaxOfDateTime: IAggregate{
      DateTime value;
      bool hasValue;
      public void Add(DateTime value){
        if (!this.hasValue || value > this.value){
          this.value = value;
          this.hasValue = true;
        }
      }
      public DateTime GetValue(){
        DateTime result = this.value;
        this.value = new DateTime();
        this.hasValue = false;
        return result;
      }
    }
    public struct MaxOfSqlByte: IAggregate{
      byte value;
      bool hasValue;
      public void Add(SqlByte value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (byte)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (byte)value;
        }
      }
      public SqlByte GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlByte.Null;
      }
    }
    public struct MaxOfSqlInt16: IAggregate{
      short value;
      bool hasValue;
      public void Add(SqlInt16 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (short)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (short)value;
        }
      }
      public SqlInt16 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt16.Null;
      }
    }
    public struct MaxOfSqlInt32: IAggregate{
      int value;
      bool hasValue;
      public void Add(SqlInt32 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (int)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (int)value;
        }
      }
      public SqlInt32 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt32.Null;
      }
    }
    public struct MaxOfSqlInt64: IAggregate{
      long value;
      bool hasValue;
      public void Add(SqlInt64 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (long)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (long)value;
        }
      }
      public SqlInt64 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt64.Null;
      }
    }
    public struct MaxOfSqlSingle: IAggregate{
      float value;
      bool hasValue;
      public void Add(SqlSingle value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value.Value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = value.Value;
        }
      }
      public SqlSingle GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlSingle.Null;
      }
    }
    public struct MaxOfSqlDouble: IAggregate{
      double value;
      bool hasValue;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (double)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (double)value;
        }
      }
      public SqlDouble GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDouble.Null;
      }
    }
    public struct MaxOfSqlDecimal: IAggregate{
      SqlDecimal value;
      bool hasValue;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = value;
        }
      }
      public SqlDecimal GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDecimal.Null;
      }
    }
    public struct MaxOfSqlMoney: IAggregate{
      SqlMoney value;
      bool hasValue;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = value;
        }
      }
      public SqlMoney GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlMoney.Null;
      }
    }
    public struct MaxOfSqlString: IAggregate{
      SqlString value;
      bool hasValue;
      public void Add(SqlString value){
        if (!value.IsNull){
          if (!this.hasValue || (bool)SqlString.GreaterThan(value, this.value)){
            this.value = value;
            this.hasValue = true;
          }
        }
      }
      public SqlString GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlString.Null;
      }
    }
    public struct MaxOfSqlDateTime: IAggregate{
      SqlDateTime value;
      bool hasValue;
      public void Add(SqlDateTime value){
        if (!value.IsNull){
          if (!this.hasValue || (bool)SqlDateTime.GreaterThan(value, this.value)){
            this.value = value;
            this.hasValue = true;
          }
        }
      }
      public SqlDateTime GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDateTime.Null;
      }
    }
  }
  public class Sum: IAggregateGroup{
    public struct SumOfInt32: IAggregate{
      int total;
      public void Add(int value){
        this.total = this.total + value;
      }
      public int GetValue(){
        int ret = this.total;
        this.total = 0;
        return ret;
      }
    }
    public struct SumOfInt64: IAggregate{
      long total;
      public void Add(long value){
        this.total = this.total + value;
      }
      public long GetValue(){
        long ret = this.total;
        this.total = 0;
        return ret;
      }
    }
    public struct SumOfDouble: IAggregate{
      double total;
      public void Add(double value){
        this.total = this.total + value;
      }
      public double GetValue(){
        double ret = this.total;
        this.total = 0.0;
        return ret;
      }
    }
    public struct SumOfDecimal: IAggregate{
      decimal total;
      public void Add(decimal value){
        this.total = this.total + value;
      }
      public decimal GetValue(){
        decimal ret = this.total;
        this.total = 0;
        return ret;
      }
    }
    public struct SumOfSqlInt32: IAggregate{
      int total;
      bool hasValue;
      public void Add(SqlInt32 value){
        if (!value.IsNull){
          if (this.hasValue)
            this.total = this.total + (int) value;
          else{
            this.total = (int) value;
            this.hasValue = true;
          }
        }
      }
      public SqlInt32 GetValue(){
        if (!this.hasValue){
          return SqlInt32.Null;
        }
        this.hasValue = false;
        return (SqlInt32) this.total;
      }
    }
    public struct SumOfSqlInt64: IAggregate{
      long total;
      bool hasValue;
      public void Add(SqlInt64 value){
        if (!value.IsNull){
          if (this.hasValue)
            this.total = this.total + (long) value;
          else{
            this.total = (long) value;
            this.hasValue = true;
          }
        }
      }
      public SqlInt64 GetValue(){
        if (!this.hasValue) return SqlInt64.Null;
        this.hasValue = false;
        return (SqlInt64) this.total;
      }
    }
    public struct SumOfSqlDouble: IAggregate{
      SqlDouble total;
      bool hasValue;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          if (this.hasValue){
            this.total = this.total + value;
          }else{
            this.total = value;
            this.hasValue = true;
          }
        }
      }
      public SqlDouble GetValue(){
        if (!this.hasValue) return SqlDouble.Null;
        this.hasValue = false;
        return this.total;
      }
    }
    public struct SumOfSqlDecimal: IAggregate{
      SqlDecimal total;
      bool hasValue;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (this.hasValue)
            this.total = this.total + value;
          else{
            this.total = value;
            this.hasValue = true;
          }
        }
      }
      public SqlDecimal GetValue(){
        if (!this.hasValue) return SqlDecimal.Null;
        this.hasValue = false;
        return this.total;
      }
    }
    public struct SumOfSqlMoney: IAggregate{
      SqlMoney total;
      bool hasValue;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (this.hasValue)
            this.total = this.total + value;
          else{
            this.total = value;
            this.hasValue = true;
          }
        }
      }
      public SqlMoney GetValue(){
        if (!this.hasValue) return SqlMoney.Null;
        this.hasValue = false;
        return this.total;
      }
    }
  }
  public class Avg: IAggregateGroup{
    public struct AvgOfInt32: IAggregate{
      long total;
      long count;
      public void Add(int value){
        this.total += value;
        this.count++;
      }
      public int GetValue(){
        int result = (int)(this.total / this.count);
        this.total = 0;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfInt64: IAggregate{
      decimal total;
      long count;
      public void Add(long value){
        this.total += value;
        this.count++;
      }
      public long GetValue(){
        long result = (long)(this.total / this.count);
        this.total = 0;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfDouble: IAggregate{
      double total;
      long count;
      public void Add(double value){
        this.total += value;
        this.count++;
      }
      public double GetValue(){
        double result = this.total / this.count;
        this.total = 0;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfDecimal: IAggregate{
      decimal total;
      long count;
      public void Add(decimal value){
        this.total += value;
        this.count++;
      }
      public decimal GetValue(){
        decimal result = this.total / this.count;
        this.total = 0;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlInt32: IAggregate{
      long total;
      long count;
      public void Add(SqlInt32 value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = (int)value;
          else
            this.total += (int)value;
          this.count++;
        }
      }
      public SqlInt32 GetValue(){
        if (this.count == 0) return SqlInt32.Null;
        int result = (int)(this.total / this.count);
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlInt64: IAggregate{
      decimal total;
      long count;
      public void Add(SqlInt64 value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = (long)value;
          else
            this.total += (long)value;
          this.count++;
        }
      }
      public SqlInt64 GetValue(){
        if (this.count == 0) return SqlInt64.Null;
        long result = (long)(this.total / this.count);
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlDouble: IAggregate{
      SqlDouble total;
      long count;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = value;
          else
            this.total += value;
          this.count++;
        }
      }
      public SqlDouble GetValue(){
        if (this.count == 0) return SqlDouble.Null;
        SqlDouble result = this.total / count;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlDecimal: IAggregate{
      SqlDecimal total;
      long count;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = value;
          else
            this.total += value;
          this.count++;
        }
      }
      public SqlDecimal GetValue(){
        if (this.count == 0) return SqlDecimal.Null;
        SqlDecimal result = this.total / count;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlMoney: IAggregate{
      SqlMoney total;
      long count;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = value;
          else
            this.total += value;
          this.count++;
        }
      }
      public SqlMoney GetValue(){
        if (this.count == 0) return SqlMoney.Null;
        SqlMoney result = this.total / count;
        this.count = 0;
        return result;
      }
    }
  }
  public class Stdev: IAggregateGroup{
    public struct StdevOfDouble: IAggregate{
      double sumX;
      double sumX2;
      int count;
      public void Add(double value){
        this.sumX += value;
        this.sumX2 += (value * value);
        this.count++;
      }
      public double GetValue(){
        int c = count - 1;
        double result = Math.Sqrt((sumX2/c) - ((sumX * sumX)/count/c));
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return result;
      }
    }
    public struct StdevOfDecimal: IAggregate{
      decimal sumX;
      decimal sumX2;
      int count;
      public void Add(decimal value){
        this.sumX += value;
        this.sumX2 += (value * value);
        this.count++;
      }
      public double GetValue(){
        int c = count - 1;
        // note: using Math.Sqrt(double) would lose precision, so use SqlDecimal.Power
        SqlDecimal result = SqlDecimal.Power((sumX2/c) - ((sumX * sumX)/count/c), 0.5);
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return (double)(SqlDouble)result;
      }
    }
    public struct StdevOfSqlDouble: IAggregate{
      double sumX;
      double sumX2;
      int count;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          double dv = (double) value;
          this.sumX += dv;
          this.sumX2 += dv * dv;
          this.count++;
        }
      }
      public SqlDouble GetValue(){
        if (this.count < 2) return SqlDouble.Null;
        int c = count - 1;
        double result = Math.Sqrt((sumX2/c) - ((sumX * sumX)/count/c));
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return (SqlDouble) result;
      }
    }
    public struct StdevOfSqlDecimal: IAggregate{
      SqlDecimal sumX;
      SqlDecimal sumX2;
      int count;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (this.count == 0){
            this.sumX = value;
            this.sumX2 = value * value;
          }else{
            this.sumX += value;
            this.sumX2 += value * value;
          }
          this.count++;
        }
      }
      public SqlDouble GetValue(){
        if (this.count < 2) return SqlDecimal.Null;
        int c = count - 1;
        SqlDecimal result = SqlDecimal.Power((sumX2/c) - ((sumX * sumX)/count/c), 0.5);
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return (SqlDouble)result;
      }
    }
    public struct StdevOfSqlMoney: IAggregate{
      SqlMoney sumX;
      SqlMoney sumX2;
      int count;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (this.count == 0){
            this.sumX = value;
            this.sumX2 = value * value;
          }else{
            this.sumX += value;
            this.sumX2 += value * value;
          }
          this.count++;
        }
      }
      public SqlDouble GetValue(){
        if (this.count < 2) return SqlMoney.Null;
        int c = count - 1;
        SqlDecimal result = SqlDecimal.Power((sumX2/c) - ((sumX * sumX)/count/c), 0.5);
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return (SqlDouble)result;
      }
    }
  }
  public class Count: IAggregateGroup{
    public struct CountOfObject: IAggregate{
      int count;
      public void Add(object value){
        count++;
      }
      public int GetValue(){
        int result = count;
        this.count = 0;
        return result;
      }
    }
  }

  [Anonymous]
  public sealed class SqlFunctions{
    public static SqlByte Abs(SqlByte value){
      return value;
    }
    public static SqlInt16 Abs(SqlInt16 value){
      if (value.IsNull) return SqlInt16.Null;
      return Math.Abs((short)value);
    }
    public static SqlInt32 Abs(SqlInt32 value){
      if (value.IsNull) return SqlInt32.Null;
      return Math.Abs((int)value);
    }
    public static SqlInt64 Abs(SqlInt64 value){
      if (value.IsNull) return SqlInt64.Null;
      return Math.Abs((long)value);
    }
    public static SqlDouble Abs(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Abs((double)value);
    }
    public static SqlDecimal Abs(SqlDecimal value){
      if (value.IsNull) return SqlDecimal.Null;
      return (value < 0) ? -value : value;
    }
    public static SqlMoney Abs(SqlMoney value){
      if (value.IsNull) return SqlMoney.Null;
      return (value < 0) ? -value : value;
    }
    public static SqlDouble Acos(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Acos((double)value);
    }
    public static SqlDouble Asin(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Asin((double)value);
    }
    public static SqlDouble Atan(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Atan((double)value);
    }
    public static SqlDouble Atn2(SqlDouble value1, SqlDouble value2){
      if (value1.IsNull || value2.IsNull) return SqlDouble.Null;
      return Math.Atan2((double)value1, (double)value2);
    }
    public static SqlByte Ceiling(SqlByte value){
      return value;
    }
    public static SqlInt16 Ceiling(SqlInt16 value){
      return value;
    }
    public static SqlInt32 Ceiling(SqlInt32 value){
      return value;
    }
    public static SqlInt64 Ceiling(SqlInt64 value){
      return value;
    }
    public static SqlDouble Ceiling(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Ceiling((double)value);
    }
    public static SqlDecimal Ceiling(SqlDecimal value){
      return SqlDecimal.Ceiling(value);
    }
    public static SqlMoney Ceiling(SqlMoney value){
      return (SqlMoney)SqlDecimal.Ceiling(value);
    }
    public static SqlInt32 CharIndex(SqlString pattern, SqlString source){
      if (pattern.IsNull || source.IsNull) return SqlInt32.Null;
      return ((string/*!*/)source.Value).IndexOf((string/*!*/)pattern.Value) + 1;
    }
    public static SqlDouble Cos(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Cos((double)value);
    }
    public static SqlDateTime DateAdd(SqlDatePart part, SqlInt32 value, SqlDateTime date){
      if (value.IsNull || date.IsNull) return SqlDateTime.Null;
      int incr = (int)value;
      DateTime dt = (DateTime)date;
      switch (part){
        case SqlDatePart.Year:
          return dt.AddYears(incr);
        case SqlDatePart.Month:
          return dt.AddMonths(incr);
        case SqlDatePart.Day:
          return dt.AddDays(incr);
        case SqlDatePart.Hour:
          return dt.AddHours(incr);
        case SqlDatePart.Minute:
          return dt.AddMinutes(incr);
        case SqlDatePart.Second:
          return dt.AddSeconds(incr);
        case SqlDatePart.Millisecond:
          return dt.AddMilliseconds(incr);
      }
      return dt;
    }
    public static SqlInt32 DatePart(SqlDatePart part, SqlDateTime date){
      if (date.IsNull) return SqlInt32.Null;
      DateTime dt = (DateTime)date;
      switch (part){
        case SqlDatePart.Year: 
          return dt.Year;
        case SqlDatePart.Month:
          return dt.Month;
        case SqlDatePart.Week:
          return (dt.DayOfYear + 6)/ 7;
        case SqlDatePart.WeekDay:
          return (int)dt.DayOfWeek;
        case SqlDatePart.Day:
          return dt.Day;
        case SqlDatePart.DayOfYear:
          return dt.DayOfYear;
        case SqlDatePart.Hour:
          return dt.Hour;
        case SqlDatePart.Minute:
          return dt.Minute;
        case SqlDatePart.Second:
          return dt.Second;
        case SqlDatePart.Millisecond:
          return dt.Millisecond;
      }
      return 0;
    }
    public static SqlDouble Degrees(SqlDouble radians){
      if (radians.IsNull) return SqlDouble.Null;
      return ((double)radians) * Math.PI / 2;
    }
    public static SqlDouble Exp(SqlDouble exponent){
      return Math.Exp((double)exponent);
    }
    public static SqlByte Floor(SqlByte value){
      return value;
    }
    public static SqlInt16 Floor(SqlInt16 value){
      return value;
    }
    public static SqlInt32 Floor(SqlInt32 value){
      return value;
    }
    public static SqlInt64 Floor(SqlInt64 value){
      return value;
    }
    public static SqlDouble Floor(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Floor((double)value);
    }
    public static SqlDecimal Floor(SqlDecimal value){
      return SqlDecimal.Floor(value);
    }
    public static SqlMoney Floor(SqlMoney value){
      return (SqlMoney)SqlDecimal.Floor(value);
    }
    public static SqlDateTime GetDate(){
      return DateTime.Now;
    }
    public static SqlDateTime GetUtcDate(){
      return DateTime.UtcNow;
    }
    public static SqlBoolean IsDate(SqlString value){
      if (value.IsNull) return SqlBoolean.Null;
      try{ DateTime.Parse((string)value); }
      catch{ return false; }
      return true;
    }
    public static SqlString Left(SqlString value, SqlInt32 length){
      if (value.IsNull || length.IsNull) return SqlString.Null;
      int len = (int)length;
      string str = (string/*!*/)value.Value;
      return str.Substring(0, len);
    }
    public static SqlInt32 Len(SqlString value){
      if (value.IsNull) return SqlInt32.Null;
      return ((string/*!*/)value.Value).Length;
    }
    public static SqlDouble Log(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Log((double)value);
    }
    public static SqlDouble Log10(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Log10((double)value);
    }
    public static SqlDouble Power(SqlDouble value, SqlDouble exponent){
      if (value.IsNull || exponent.IsNull) return SqlDouble.Null;
      return Math.Pow((double)value, (double)exponent);
    }
    public static SqlString Replace(SqlString source, SqlString oldValue, SqlString newValue){
      if (source.IsNull || oldValue.IsNull || newValue.IsNull) return SqlString.Null;
      return ((string/*!*/)source.Value).Replace((string/*!*/)oldValue.Value, (string/*!*/)newValue.Value);
    }
    public static SqlString Reverse(SqlString value){
      if (value.IsNull) return SqlString.Null;
      string str = (string/*!*/)value.Value;
      StringBuilder sb = new StringBuilder(str.Length);
      for(int i = str.Length - 1; i >= 0; i--)
        sb.Append(str[i]);       
      return sb.ToString();
    }
    public static SqlString Right(SqlString value, SqlInt32 length){
      if (value.IsNull || length.IsNull) return SqlString.Null;
      string str = (string/*!*/)value.Value;
      int len = Math.Min((int)length, str.Length);
      return str.Substring(str.Length - len - 1, len);
    }
    public static SqlDouble Round(SqlDouble value, SqlInt32 precision){
      if (value.IsNull || precision.IsNull) return SqlDouble.Null;
      return Math.Round((double)value, (int)precision);
    }
    public static SqlDecimal Round(SqlDecimal value, SqlInt32 precision){
      if (value.IsNull || precision.IsNull) return SqlDecimal.Null;
      return SqlDecimal.Round(value, (int)precision);
    }
    public static SqlMoney Round(SqlMoney value, SqlInt32 precision){
      if (value.IsNull || precision.IsNull) return SqlMoney.Null;
      return (SqlMoney) SqlDecimal.Round(value, (int)precision);
    }
    public static SqlDouble Sin(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Sin((double)value);
    }
    public static SqlString Stuff(SqlString source, SqlInt32 position, SqlInt32 length, SqlString value){
      if (source.IsNull || position.IsNull || length.IsNull) return SqlString.Null;
      int offset = ((int)position) - 1;
      string result = ((string/*!*/)source.Value).Remove(offset, (int)length);
      //^ assume result != null;
      if (!value.IsNull) result = result.Insert(offset, (string/*!*/)value.Value);
      //^ assume result != null;
      return result;
    }
    public static SqlString Substring(SqlString source, SqlInt32 position, SqlInt32 length){
      if (source.IsNull || position.IsNull || length.IsNull) return SqlString.Null;
      int offset = ((int)position) - 1;
      return ((string/*!*/)source.Value).Substring(offset, (int)length);
    }
  }

  [Anonymous]
  public enum SqlDatePart{
    Year,
    Quarter,
    Month,
    Day,
    DayOfYear,
    Week,
    WeekDay,
    Hour,
    Minute,
    Second,
    Millisecond
  }

  [Anonymous]
  public enum SqlHint{
    HoldLock,
    Serializable,
    RepeatableRead,
    ReadCommitted,
    ReadUncommitted,
    NoLock, 
    RowLock,
    PageLock,
    TableLock,
    TableLockExclusive,
    ReadPast,
    UpdateLock,
    ExclusiveLock,
  }
}
#endif
#else
#if CCINamespace
namespace Microsoft.Cci{
#else
namespace System.Compiler{
#endif
  /// <summary>
  /// Tells a sympathetic compiler that the name of the entity bearing this attribute should be suppressed. When applied to a class or enum,
  /// this means that the members of the class or enum should be injected into the same scope as would have contained the class/enum name.
  /// When applied to a field or property, it means that the members of structure of the type of the field/property should be visible
  /// without qualification by the field/property name.
  /// </summary>
  [AttributeUsage(AttributeTargets.Field|AttributeTargets.Property|AttributeTargets.Class|AttributeTargets.Enum)]
  public sealed class AnonymousAttribute: Attribute{
    private Anonymity type;
    public AnonymousAttribute(){
      this.type = Anonymity.Structural;
    }
    public Anonymity Anonymity{
      get {return this.type;}
    }
  }  
  public enum Anonymity{
    Unknown,
    None,
    Structural,
    Full
  }
  public enum CciMemberKind{
    Unknown,
    Regular,
    Auxiliary,
    FrameGuardGetter,
  }
  [AttributeUsage(AttributeTargets.All)]
  public class CciMemberKindAttribute: Attribute{
    public CciMemberKind Kind;
    public CciMemberKindAttribute(CciMemberKind kind){
      this.Kind = kind;
    }
  }
  [AttributeUsage(AttributeTargets.Class)]
  public sealed class ComposerAttribute: Attribute{
    public string AssemblyName = null;
    public string TypeName = null;
    public ComposerAttribute(){
    }
  }
  [AttributeUsage(AttributeTargets.Assembly|AttributeTargets.Module, AllowMultiple=true)]
  public sealed class CustomVisitorAttribute : Attribute{
    public string Assembly;
    public string Class;
    public string Phase;
    public bool Replace;
    public CustomVisitorAttribute(){
    }
  }
  [AttributeUsage(AttributeTargets.Class|AttributeTargets.Field|AttributeTargets.Property|AttributeTargets.Method)]
  public sealed class ElementTypeAttribute: Attribute{
    public Type ElementType = null;
    public ElementTypeAttribute(){
    }
  }
  public interface ITemplateParameter{
  }
  [AttributeUsage(AttributeTargets.Class|AttributeTargets.Delegate|AttributeTargets.Interface|AttributeTargets.Struct)]
  public sealed class TemplateAttribute : System.Attribute{
    public Type[] TemplateParameters;
    public TemplateAttribute(params Type[] parameters){
      this.TemplateParameters = parameters;
    }
  }
  [AttributeUsage(AttributeTargets.Class|AttributeTargets.Delegate|AttributeTargets.Interface|AttributeTargets.Struct)]
  public sealed class TemplateInstanceAttribute : System.Attribute{
    public Type Template;
    public Type[] TemplateArguments;
    public TemplateInstanceAttribute(Type template, params Type[] arguments){
      this.Template = template;
    }
  }

  [AttributeUsage(AttributeTargets.Class|AttributeTargets.Interface|AttributeTargets.Struct)]
  public sealed class TemplateParameterFlagsAttribute : System.Attribute{
    public int Flags;
    public TemplateParameterFlagsAttribute(int flags) {
      this.Flags = flags;
    }
  }
  namespace Diagnostics{
    public sealed class Debug{
      public static void Assert(bool condition){
        System.Diagnostics.Debug.Assert(condition);
      }
    }
  }
}
#if !NoData && !ROTOR
namespace System.Data{
  public interface IDbTransactable{
    IDbTransaction BeginTransaction();
    IDbTransaction BeginTransaction(IsolationLevel level);
  }
}
#endif
namespace StructuralTypes{
#if CCINamespace
  using Microsoft.Cci;
#else
  using System.Compiler;
#endif
  using System.Collections.Generic;
 
  public interface IConstrainedType{}
  public interface ITupleType{}
  public interface ITypeUnion{}
  public interface ITypeIntersection{}
  public interface ITypeAlias{}
  public interface ITypeDefinition{}

  [Template(typeof(ElementType))]
  public struct Boxed_1 : IEnumerable_1{
    private ElementType[] box;
    public Boxed_1(ElementType value){
      this.box = new ElementType[]{value};
    }
    public ElementType GetValue(){
      return this.box[0];
    }
    public void SetValue(ElementType value){
      this.box[0] = value;
    }
    public object ToObject(){
      if (this.box == null) return null;
      return this.box[0];
    }
    public bool IsNull(){
      return this.box == null;
    }
    IEnumerator_1 IEnumerable_1.GetEnumerator(){
      return new BoxedEnumerator_1(this.box);
    }
    public BoxedEnumerator_1 GetEnumerator(){
      return new BoxedEnumerator_1(this.box);
    }
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator(){
      return new BoxedEnumerator_1(this.box);
    }
    public void Clear(){
      this.box = null;
    }
    public static implicit operator Boxed_1(ElementType value){
      return new Boxed_1(value);
    }
    public static explicit operator ElementType(Boxed_1 boxed){
      return boxed.GetValue();
    }
    public static bool operator ==(Boxed_1 a, Boxed_1 b){
      if (a.box == null || b.box == null) return false;
      return a.box[0].Equals(b.box[0]);
    }
    public static bool operator ==(Boxed_1 a, object o){
      return a.Equals(o);
    }
    public static bool operator !=(Boxed_1 a, object o){
      return !a.Equals(o);
    }
    public static bool operator ==(object o, Boxed_1 b){
      return b.Equals(o);
    }
    public static bool operator !=(object o, Boxed_1 b){
      return !b.Equals(o);
    }
    public static bool operator !=(Boxed_1 a, Boxed_1 b){
      if (a.box == null || b.box == null) return false;
      return !a.box[0].Equals(b.box[0]);
    }
    public override bool Equals(object o){
      if (this.box == null) return o == null;
      if (!(o is Boxed_1)) return false;
      Boxed_1 b = (Boxed_1)o;
      if (this.box == null || b.box == null) return this.box == b.box;
      return this.box[0].Equals(b.box[0]);
    }
    public override int GetHashCode(){
      return this.box[0].GetHashCode();
    }
  }
  [Template(typeof(ElementType))]
  public struct BoxedEnumerator_1: IEnumerator_1{
    private ElementType[] box;
    private int index;
    internal BoxedEnumerator_1(ElementType[] box){
      this.box = box;
      this.index = -1;
    }
    public ElementType Current{
      get { 
        return this.box[0];
      }
    }
    object System.Collections.IEnumerator.Current{
      get{
        return this.box[0];
      }
    }
    void System.Collections.IEnumerator.Reset(){
      this.index = -1;
    }
    void IDisposable.Dispose(){
    }
    public bool MoveNext(){
      if (this.box == null) return false;
      return ++this.index == 0;
    }
  }
  [Template(typeof(ElementType))]
  public struct Invariant_1{
    private ElementType value;
    public Invariant_1(ElementType value){
      if (value == null) throw new ArgumentNullException();
      if (value.GetType() != typeof(ElementType)) throw new ArgumentException();
      this.value = value;
    }
    public ElementType GetValue(){
      return this.value;
    }
    public object ToObject(){
      return this.value;
    }
    public static implicit operator ElementType(Invariant_1 invariantValue){
      return invariantValue.value;
    }
    public static implicit operator NonNull_1(Invariant_1 invariantValue){
      return new NonNull_1(invariantValue.value);
    }
    public static explicit operator Invariant_1(ElementType value){
      return new Invariant_1(value);
    }
  }
  [Template(typeof(ElementType))]
  public struct NonNull_1 : IEnumerable_1{
    private ElementType value;
    public NonNull_1(ElementType value){
      if (value == null) throw new ArgumentNullException();
      this.value = value;
    }
    public ElementType GetValue(){
      return this.value;
    }
    public object ToObject(){
      return this.value;
    }
    IEnumerator_1 IEnumerable_1.GetEnumerator(){
      return new ValueEnumerator_1(this.value);
    }
    public ValueEnumerator_1 GetEnumerator(){
      return new ValueEnumerator_1(this.value);
    }
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator(){
      return new ValueEnumerator_1(this.value);
    }
    public static implicit operator ElementType(NonNull_1 nonNullValue){
      return nonNullValue.value;
    }
    public static explicit operator NonNull_1(ElementType value){
      return new NonNull_1(value);
    }
  }
  [Template(typeof(ElementType))]
  public struct NonEmptyIEnumerable_1 : IEnumerable_1{
    IEnumerable_1 enumerable;
    public NonEmptyIEnumerable_1(IEnumerable_1 enumerable){
      this.enumerable = enumerable;
      if (enumerable == null) 
        throw new ArgumentNullException();
      IEnumerator_1 enumerator = enumerable.GetEnumerator();
      if (enumerator == null || !enumerator.MoveNext())
        throw new ArgumentException();
    }
    public NonEmptyIEnumerable_1(ElementType element){
      this.enumerable = new NonNull_1(element);
    }
    public ElementType GetValue(){
      IEnumerator_1 e = this.enumerable.GetEnumerator();
      if (e.MoveNext()){
        ElementType result = e.Current;
        if (!e.MoveNext()) return result;
      }
      throw new ArgumentOutOfRangeException();
    }
    public object ToObject(){
      if (this.enumerable is NonNull_1){
        NonNull_1 nnull = (NonNull_1)this.enumerable;
        return nnull.ToObject();
      }
      if (this.enumerable is Boxed_1){
        Boxed_1 boxed = (Boxed_1)this.enumerable;
        return boxed.ToObject();
      }
      return this.enumerable;
    }
    public IEnumerator_1 GetEnumerator(){
      return this.enumerable.GetEnumerator();
    }
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator(){
      return this.enumerable.GetEnumerator();
    }
    public static implicit operator NonEmptyIEnumerable_1(NonNull_1 element){
      return new NonEmptyIEnumerable_1((IEnumerable_1)element);
    }
    public static explicit operator NonEmptyIEnumerable_1(ElementType element){
      return new NonEmptyIEnumerable_1(element);
    }
    public static explicit operator NonEmptyIEnumerable_1(Boxed_1 element){
      return new NonEmptyIEnumerable_1((IEnumerable_1)element);
    }
    public static explicit operator NonEmptyIEnumerable_1(ElementType[] array){
      return new NonEmptyIEnumerable_1(new ArrayToIEnumerableAdapter_1(array));
    }
    public static explicit operator NonEmptyIEnumerable_1(List_1 list){
      return new NonEmptyIEnumerable_1(list);
    }
    public static explicit operator ElementType(NonEmptyIEnumerable_1 nonEmptyIEnumerable){
      return nonEmptyIEnumerable.GetValue();
    }
  }
  [Template(typeof(ElementType))]
  public sealed class Unboxer_1{
    public static object ToObject(IEnumerable_1 collection){
      if (collection is NonNull_1)
        return ((NonNull_1)collection).ToObject();
      if (collection is Boxed_1)
        return ((Boxed_1)collection).ToObject();
      return collection;
    }
  }

  [Template(typeof(ElementType))]
  public sealed class ArrayToIEnumerableAdapter_1 : IEnumerable_1{
    private ElementType[] array;
    public ArrayToIEnumerableAdapter_1(ElementType[] array){
      this.array = array;
    }
    public IEnumerator_1 GetEnumerator(){
      return new ArrayEnumerator_1(this.array); 
    }
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator(){
      return new ArrayEnumerator_1(this.array); 
    }
  }
  [Template(typeof(ElementType))]
  public sealed class GenericIEnumerableToGenericIListAdapter_1 : IList_1{
    private List_1 list;
    private IEnumerable_1 collection;
    public GenericIEnumerableToGenericIListAdapter_1(IEnumerable_1 collection){
      this.collection = collection;
    }

    private List_1 List{  
      get{
        List_1 result = this.list;
        if (result == null){
          result = new List_1();
          this.list = result;
          if (this.collection != null){
            IEnumerator_1 enumerator = this.collection.GetEnumerator();
            if (enumerator != null){
              while (enumerator.MoveNext()){
                ElementType curr = enumerator.Current;
                result.Add(curr);
              }
            }
          }
        }
        return result;
      }
    }
    public IEnumerator_1 GetEnumerator(){
      if (this.list != null)
        return this.list.GetEnumerator();
      else
        return this.collection.GetEnumerator();
    }
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator(){
      return this.GetEnumerator(); 
    }
    public int Count{
      get{
        return this.List.Count;
      }
    }
    public bool IsSynchronized{
      get{
        return false;
      }
    }
    public object SyncRoot{
      get{
        return this;
      }
    }
    public void CopyTo(Array array, int index){
      this.List.CopyTo(array, index);
    }
    public void CopyTo(ElementType[] array, int index){
      this.List.CopyTo(array, index);
    }

    public bool IsFixedSize{
      get{
        return false;
      }
    }
    public bool IsReadOnly{
      get{
        return false;
      }
    }
    public ElementType this[int index]{
      get{
        return this.List[index];
      }
      set{
        this.List[index] = value;
      }
    }
    public void Add(ElementType value){
      this.List.Add(value);
    }
    public void Clear(){
      this.List.Clear();
    }
    public bool Contains(ElementType value){
      return this.List.Contains(value);
    }
    public int IndexOf(ElementType value){
      return this.List.IndexOf(value);
    }
    public void Insert(int index, ElementType value){
      this.List.Insert(index, value);
    }
    public bool Remove(ElementType value){
      return this.List.Remove(value);
    }
    public void RemoveAt(int index){
      this.List.RemoveAt(index);
    }
  }
  [Template(typeof(ElementType))]
  public struct ValueEnumerator_1: IEnumerator_1{
    private ElementType value;
    private int index;

    public ValueEnumerator_1(ElementType value){
      this.value = value;
      this.index = -1;
    }

    public ElementType Current{
      get{
        return this.value;
      }
    }
    object System.Collections.IEnumerator.Current{
      get{
        return this.value;
      }
    }
    void System.Collections.IEnumerator.Reset(){
      this.index = -1;
    }
    void IDisposable.Dispose(){
    }
    public bool MoveNext(){
      return ++this.index == 0;
    }
  }

  [Template(typeof(ElementType))]
  public sealed class StreamUtility_1{
    private StreamUtility_1(){}
    public static bool IsNull(IEnumerable_1 stream){
      if (stream == null) return true;
      IEnumerator_1 enumerator = stream.GetEnumerator();
      while (enumerator.MoveNext())
        if (enumerator.Current != null) return false;
      return true;
    }
  }
}
namespace System{
#if CCINamespace
  using Microsoft.Cci;
#else
  using System.Compiler;
#endif
  using System.Collections.Generic;

  [Template(typeof(ElementType))]
  public struct Nullable_1{
    internal ElementType value;
    internal bool hasValue;
    
    public Nullable_1(ElementType value){
      this.value = value;
      this.hasValue = true;
    }

    public override bool Equals(object other){
      if (other is Nullable_1)
        return Nullable_1.Equals(this, (Nullable_1)other);
      return false;
    }

    public override int GetHashCode(){
      return hasValue ? value.GetHashCode() : 0;
    }

    public override string ToString(){
      return hasValue ? value.ToString() : "";
    }        

    public bool HasValue{
      get{
        return hasValue;
      }
    }

    public ElementType Value{
      get{
        if (!hasValue)
          throw new InvalidOperationException();
        return value;
      }
    }

    public bool Equals(Nullable_1 other){        
      return Nullable_1.Equals(this, other);
    }

    public ElementType GetValueOrDefault(){
      return value;
    }

    public ElementType GetValueOrDefault(ElementType defaultValue){
      return hasValue ? value : defaultValue;
    }

    public static implicit operator Nullable_1(ElementType value){
      return new Nullable_1(value);
    }

    public static explicit operator ElementType(Nullable_1 value){
      return value.Value;
    }
  }
}
namespace System.Collections.Generic{
#if CCINamespace
  using Microsoft.Cci;
#else
  using System.Compiler;
#endif
  using StructuralTypes;
  using SCIEnumerable = System.Collections.IEnumerable;
  using SCIEnumerator = System.Collections.IEnumerator;
  using SCIList = System.Collections.IList;

  public class ElementType : ITemplateParameter{
  }

  [Template(typeof(ElementType))]
  public interface IEnumerable_1 : SCIEnumerable{
    [return:Microsoft.Contracts.NotNull]
    new IEnumerator_1 GetEnumerator();
  }

  [Template(typeof(ElementType))]
  public interface ICollection_1 : IEnumerable_1, SCIEnumerable{
    int Count {get;}
    void Add(ElementType e);
    void Clear();
    bool Contains(ElementType e);
    void CopyTo(ElementType[] array, int index);
    bool Remove(ElementType e);
    bool IsReadOnly { get; }
  }

  [Template(typeof(ElementType))]
  public interface IList_1 : ICollection_1, IEnumerable_1, IEnumerable{
    ElementType this[int index] {get; set;}
    int IndexOf(ElementType value);
    void Insert(int index, ElementType value);
    void RemoveAt(int index);
  }
  [Template(typeof(ElementType))]
  public sealed class Stack_1 : IEnumerable_1, ICollection, IEnumerable{
    private ElementType[] elements;
    private int capacity;
    private int count;
    public Stack_1(){
      this.capacity = 0;
      this.count = 0;
    }
    public Stack_1(int capacity){
      this.capacity = capacity;
      this.count = 0;
      this.elements = new ElementType[capacity];
    }
    public int Count{
      get{
        return this.count;
      }
    }
    public void CopyTo(Array array, int index){
      ElementType[] elements = this.elements;
      int n = this.count;
      for (int i = 0; i < n; i++){
        object elem = elements[i];
        array.SetValue(elem, index++);
      }
    }
    public bool IsSynchronized{
      get{
        return false;
      }
    }
    public bool IsReadOnly{
      get{
        return false;
      }
    }
    public object SyncRoot{
      get{
        return this;
      }
    }
    IEnumerator_1 IEnumerable_1.GetEnumerator(){
      return new StackEnumerator_1(this);
    }
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator(){
      return new StackEnumerator_1(this);
    }
    public object Clone(){
      Stack_1 s = new Stack_1(this.capacity);
      for (int i = 0, n = this.count; i < n; i++)
        s.elements[i] = this.elements[i];
      return s; //REVIEW: should this clone the elements too?
    }
    private void DoubleCapacity(){
      int oldCapacity = this.capacity;
      if (oldCapacity == 0){
        this.capacity = 16;
        this.elements = new ElementType[16];
        return;
      }
      this.capacity = oldCapacity*2;
      ElementType[] oldElements = this.elements;
      ElementType[] newElements = this.elements = new ElementType[this.capacity];
      for (int i = 0, n = this.count; i < n; i++)
        newElements[i] = oldElements[i];
    }
    public void Push(ElementType e){
      int i = this.count;
      int ip1 = i+1;
      if (ip1 > this.capacity) this.DoubleCapacity();
      this.elements[i] = e;
      this.count = ip1;
      return;
    }
    public ElementType Pop(){
      if (this.count == 0)
        throw new InvalidOperationException("Stack.Pop: empty stack");
      return this.elements[--this.count];
    }
    public bool Empty(){
      return this.count == 0;
    }
    public ElementType Peek(){
      if (this.count == 0)
        throw new InvalidOperationException("Stack.Peek: empty stack");
      return this.elements[this.count-1];
    }
    public void Clear() {
      this.count = 0;
    }
  }
  [Template(typeof(ElementType))]
  public struct StackEnumerator_1: IEnumerator_1, SCIEnumerator{
    private ElementType[] contents;
    private int index;
    private int count;

    public StackEnumerator_1(Stack_1 stack){
      this.count = stack.Count;
      this.contents = new ElementType[this.count];
      stack.CopyTo(contents,0);
      this.index = -1;
    }

    public ElementType Current{
      get{
        return this.contents[this.index];
      }
    }
    object SCIEnumerator.Current{
      get{
        return this.contents[this.index];
      }
    }
    void IDisposable.Dispose(){
    }
    public bool MoveNext(){
      return ++this.index < this.count;
    }
    public void Reset(){
      this.index = -1;
    }
  }
  [Template(typeof(ElementType))]
  public sealed class List_1 : IList_1, ICollection_1, IEnumerable_1, SCIList, ICollection, IEnumerable{
    private ElementType[] elements;
    private int capacity;
    private int count;

    public List_1(){
      this.capacity = 0;
      this.count = 0;
    }
    public List_1(int capacity){
      this.capacity = capacity;
      this.count = 0;
      this.elements = new ElementType[capacity];
    }
    public List_1(IEnumerable_1 collection)
      : this(16){
      IEnumerator_1 enumerator = collection.GetEnumerator();
      while (enumerator.MoveNext())
        this.Add(enumerator.Current);
    }

    public ListEnumerator_1 GetEnumerator(){
      return new ListEnumerator_1(this);
    }
    IEnumerator_1 IEnumerable_1.GetEnumerator(){
      return new ListEnumerator_1(this);
    }
    SCIEnumerator SCIEnumerable.GetEnumerator(){
      return new ListEnumerator_1(this);
    }
    public int Capacity{
      get{
        return this.capacity;
      }
      set{
        if (value < this.count) throw new ArgumentOutOfRangeException("value");
        ElementType[] oldElements = this.elements;
        ElementType[] newElements = this.elements = new ElementType[this.capacity = value];
        for (int i = 0, n = this.count; i < n; i++)
          newElements[i] = oldElements[i];
      }
    }
    public int Count{
      get{
        return this.count;
      }
    }
    public bool IsSynchronized{
      get{
        return false;
      }
    }
    public object SyncRoot{
      get{
        return this;
      }
    }
    public void CopyTo(Array array, int index){
      ElementType[] elements = this.elements;
      int n = this.count;
      for (int i = 0; i < n; i++){
        object elem = elements[i];
        array.SetValue(elem, index++);
      }
    }
    public void CopyTo(ElementType[] array, int index){
      ElementType[] elements = this.elements;
      int n = this.count;
      for (int i = 0; i < n; i++){
        object elem = elements[i];
        array.SetValue(elem, index++);
      }
    }
    private void DoubleCapacity(){
      int oldCapacity = this.capacity;
      if (oldCapacity == 0){
        this.capacity = 16;
        this.elements = new ElementType[16];
        return;
      }
      this.Capacity = oldCapacity*2;
    }
    public bool IsFixedSize{
      get{
        return false;
      }
    }
    public bool IsReadOnly{
      get{
        return false;
      }
    }
    public ElementType this[int index]{
      get{
        if (index < 0 || index >= this.count) throw new ArgumentOutOfRangeException("index");
        return this.elements[index];
      }
      set{
        if (index < 0 || index >= this.count) throw new ArgumentOutOfRangeException("index");
        this.elements[index] = value;
      }
    }
    object SCIList.this[int index]{
      get{
        return this[index];
      }
      set{
        this[index] = (ElementType)value;
      }
    }
    public void Add(ElementType value){
      int i = this.count;
      int ip1 = i+1;
      if (ip1 > this.capacity) this.DoubleCapacity();
      this.elements[i] = value;
      this.count = ip1;
    }
    int SCIList.Add(object value){
      int i = this.count;
      this.Add((ElementType)value);
      return i;
    }
    public void Clear(){
      this.count = 0;
    }
    public bool Contains(ElementType value){
      return this.IndexOf(value) >= 0;
    }
    bool SCIList.Contains(object value){
      return ((SCIList)this).IndexOf(value) >= 0;
    }
    public int IndexOf(ElementType value){
      return Array.IndexOf(this.elements, value, 0, this.count);
    }
    int SCIList.IndexOf(object value){
      return Array.IndexOf(this.elements, value, 0, this.count);
    }
    public void Insert(int index, ElementType value){
      if (index < 0 || index > this.count) throw new ArgumentOutOfRangeException("index");
      if (index == this.count)
        this.Add(value);
      else{
        int i = this.count;
        int ip1 = i+1;
        if (ip1 > this.capacity) this.DoubleCapacity();
        Array.Copy(this.elements, index, this.elements, index + 1, this.count - index);
        this.elements[index] = value;
      }
    }
    void SCIList.Insert(int index, object value){
      this.Insert(index, (ElementType)value);
    }
    public bool Remove(ElementType value){
      object oval = value;
      for(int i = 0; i < this.count; i++){
        object oval2 = this.elements[i];
        if (oval2 == oval || (oval2 != null && oval2.Equals(oval))){
          this.RemoveAt(i);
          return true;
        }
      }
      return false;
    }
    void SCIList.Remove(object value){
      this.Remove((ElementType)value);
    }
    public void RemoveAt(int index){
      if (index < 0 || index > count) throw new ArgumentOutOfRangeException("index");
      if (index < count - 1){
        Array.Copy(this.elements, index + 1, this.elements, index, count - index);
      }
      this.count -= 1;
    }
    public object Clone(){
      return new List_1(this); //REVIEW: should this clone the elements too?
    }
    public void AddRange(IEnumerable_1 elts){
      foreach (ElementType o in elts)
        this.Add(o);
    }
    public ICollection_1 AsReadOnly(){
      return this;
    }
  }

  [Template(typeof(ElementType))]
  public sealed class Queue_1 : IEnumerable_1, System.Collections.ICollection, IEnumerable{
    private ElementType[] elements;
    private int capacity;
    private int count;

    public Queue_1(){
      this.capacity = 0;
      this.count = 0;
    }
    public Queue_1(int capacity){
      this.capacity = capacity;
      this.count = 0;
      this.elements = new ElementType[capacity];
    }
    public Queue_1(IEnumerable_1 collection)
      : this(16){
      IEnumerator_1 enumerator = collection.GetEnumerator();
      while (enumerator.MoveNext())
        this.Enqueue(enumerator.Current);
    }

    public ArrayEnumerator_1 GetEnumerator(){
      return new ArrayEnumerator_1(this.elements);
    }
    IEnumerator_1 IEnumerable_1.GetEnumerator(){
      return new ArrayEnumerator_1(this.elements);
    }
    SCIEnumerator SCIEnumerable.GetEnumerator(){
      return new ArrayEnumerator_1(this.elements);
    }
    public int Capacity{
      get{
        return this.capacity;
      }
      set{
        if (value < this.count) throw new ArgumentOutOfRangeException("value");
        ElementType[] oldElements = this.elements;
        ElementType[] newElements = this.elements = new ElementType[this.capacity = value];
        for (int i = 0, n = this.count; i < n; i++)
          newElements[i] = oldElements[i];
      }
    }
    public int Count{
      get{
        return this.count;
      }
    }
    public bool IsSynchronized{
      get{
        return false;
      }
    }
    public object SyncRoot{
      get{
        return this;
      }
    }
    public void CopyTo(Array array, int index){
      ElementType[] elements = this.elements;
      int n = this.count;
      for (int i = 0; i < n; i++){
        object elem = elements[i];
        array.SetValue(elem, index++);
      }
    }
    private void DoubleCapacity(){
      int oldCapacity = this.capacity;
      if (oldCapacity == 0){
        this.capacity = 16;
        this.elements = new ElementType[16];
        return;
      }
      this.Capacity = oldCapacity*2;
    }
    public bool IsFixedSize{
      get{
        return false;
      }
    }
    public bool IsReadOnly{
      get{
        return false;
      }
    }
    public void Enqueue(ElementType value){
      int i = this.count;
      int ip1 = i+1;
      if (ip1 > this.capacity) this.DoubleCapacity();
      this.elements[i] = value;
      this.count = ip1;
    }
    public void Clear(){
      this.count = 0;
    }
    public bool Contains(ElementType value){
      return Array.IndexOf(this.elements, value, 0, this.count) >= 0;
    }
    public ElementType Dequeue(){
      if (this.count == 0){
        throw new InvalidOperationException();
      }
      ElementType oval = this.elements[0];
      for(int i = 0; i < this.count-1; i++){
        this.elements[i] = this.elements[i+1];
      }
      this.count--;
      return oval;
    }
    public ElementType Peek(){
      if (this.count == 0){
        throw new InvalidOperationException();
      }
      return this.elements[0];
    }
    public object Clone(){
      return new Queue_1(this); //REVIEW: should this clone the elements too?
    }
  }

  [Template(typeof(ElementType))]
  public interface IEnumerator_1 : IDisposable, SCIEnumerator{
    new ElementType Current{get;}
  }

  [Template(typeof(ElementType))]
  public struct ArrayEnumerator_1: IEnumerator_1, SCIEnumerator{
    private ElementType[] array;
    private int index;

    public ArrayEnumerator_1(ElementType[] array){
      this.array = array;
      this.index = -1;
    }

    public ElementType Current{
      get{
        return this.array[this.index];
      }
    }
    object SCIEnumerator.Current{
      get{
        return this.array[this.index];
      }
    }
    void IDisposable.Dispose(){
    }
    public bool MoveNext(){
      return ++this.index < this.array.Length;
    }
    void SCIEnumerator.Reset(){
      this.index = -1;
    }
  }

  [Template(typeof(ElementType))]
  public struct ListEnumerator_1: IEnumerator_1, SCIEnumerator{
    private List_1 list;
    private int index;

    public ListEnumerator_1(List_1 list){
      this.list = list;
      this.index = -1;
    }

    public ElementType Current{
      get{
        return this.list[this.index];
      }
    }
    object SCIEnumerator.Current{
      get{
        return this.list[this.index];
      }
    }
    void IDisposable.Dispose(){
    }
    public bool MoveNext(){
      return ++this.index < this.list.Count;
    }
    public void Reset(){
      this.index = -1;
    }
  }
}

#if !NoData && !ROTOR
namespace System.Query{
#if CCINamespace
  using Microsoft.Cci;
#else
  using System.Compiler;
#endif
  using System.Collections.Generic;
  using System.Data.SqlTypes;
  using System.Text;

  //TODO: this class should derive from SystemException and it should not contain a string
  //The message, if any, should be obtained from a resource file
  public class StreamNotSingletonException: Exception{
    public StreamNotSingletonException(): base("Stream not singleton"){
    }
  }
  
  public interface IAggregate{
  }
  public interface IAggregateGroup{
  }

  public class Min: IAggregateGroup{
    public struct MinOfByte: IAggregate{
      byte value;
      bool hasValue;
      public void Add(byte value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value){
          this.value = value;
        }
      }
      public byte GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfInt16: IAggregate{
      short value;
      bool hasValue;
      public void Add(short value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value){
          this.value = value;
        }
      }
      public short GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfInt32: IAggregate{
      int value;
      bool hasValue;
      public void Add(int value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value){
          this.value = value;
        }
      }
      public int GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfInt64: IAggregate{
      long value;
      bool hasValue;
      public void Add(long value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value)
          this.value = value;
      }
      public long GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfSingle: IAggregate{
      float value;
      bool hasValue;
      public void Add(float value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value){
          this.value = value;
        }
      }
      public float GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfDouble: IAggregate{
      double value;
      bool hasValue;
      public void Add(double value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value)
          this.value = value;
      }
      public double GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfDecimal: IAggregate{
      decimal value;
      bool hasValue;
      public void Add(decimal value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value < this.value)
          this.value = value;
      }
      public decimal GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MinOfString: IAggregate{
      string value;
      public void Add(string value){
        if (value != null){
          if (this.value == null || value.CompareTo(this.value) < 0)
            this.value = value;
        }
      }
      public string GetValue(){
        string result = this.value;
        this.value = null;
        return result;
      }
    }
    public struct MinOfDateTime: IAggregate{
      DateTime value;
      bool hasValue;
      public void Add(DateTime value){
        if (!this.hasValue || value < this.value){
          this.value = value;
          this.hasValue = true;
        }
      }
      public DateTime GetValue(){
        DateTime result = this.value;
        this.value = new DateTime();
        this.hasValue = false;
        return result;
      }
    }
    public struct MinOfSqlByte: IAggregate{
      byte value;
      bool hasValue;
      public void Add(SqlByte value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (byte)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (byte)value;
          }
        }
      }
      public SqlByte GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlByte.Null;
      }
    }
    public struct MinOfSqlInt16: IAggregate{
      short value;
      bool hasValue;
      public void Add(SqlInt16 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (short)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (short)value;
          }
        }
      }
      public SqlInt16 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt16.Null;
      }
    }
    public struct MinOfSqlInt32: IAggregate{
      int value;
      bool hasValue;
      public void Add(SqlInt32 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (int)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (int)value;
          }
        }
      }
      public SqlInt32 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt32.Null;
      }
    }
    public struct MinOfSqlInt64: IAggregate{
      long value;
      bool hasValue;
      public void Add(SqlInt64 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (long)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (long)value;
          }
        }
      }
      public SqlInt64 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt64.Null;
      }
    }
    public struct MinOfSqlSingle: IAggregate{
      float value;
      bool hasValue;
      public void Add(SqlSingle value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value.Value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = value.Value;
          }
        }
      }
      public SqlSingle GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlSingle.Null;
      }
    }
    public struct MinOfSqlDouble: IAggregate{
      double value;
      bool hasValue;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (double)value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = (double)value;
          }
        }
      }
      public SqlDouble GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDouble.Null;
      }
    }
    public struct MinOfSqlDecimal: IAggregate{
      SqlDecimal value;
      bool hasValue;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = value;
          }
        }
      }
      public SqlDecimal GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDecimal.Null;
      }
    }
    public struct MinOfSqlMoney: IAggregate{
      SqlMoney value;
      bool hasValue;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value;
            this.hasValue = true;
          }
          if (value < this.value){
            this.value = value;
          }
        }
      }
      public SqlMoney GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlMoney.Null;
      }
    }
    public struct MinOfSqlString: IAggregate{
      SqlString value;
      bool hasValue;
      public void Add(SqlString value){
        if (!value.IsNull){
          if (!this.hasValue || (bool)SqlString.LessThan(value, this.value)){
            this.value = value;
            this.hasValue = true;
          }
        }
      }
      public SqlString GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlString.Null;
      }
    }
    public struct MinOfSqlDateTime: IAggregate{
      SqlDateTime value;
      bool hasValue;
      public void Add(SqlDateTime value){
        if (!value.IsNull){
          if (!this.hasValue || (bool)SqlDateTime.LessThan(value, this.value)){
            this.value = value;
            this.hasValue = true;
          }
        }
      }
      public SqlDateTime GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDateTime.Null;
      }
    }
  }
  public class Max: IAggregateGroup{
    public struct MaxOfByte: IAggregate{
      byte value;
      bool hasValue;
      public void Add(byte value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public byte GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfInt16: IAggregate{
      short value;
      bool hasValue;
      public void Add(short value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public short GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfInt32: IAggregate{
      int value;
      bool hasValue;
      public void Add(int value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public int GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfInt64: IAggregate{
      long value;
      bool hasValue;
      public void Add(long value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public long GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfSingle: IAggregate{
      float value;
      bool hasValue;
      public void Add(float value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public float GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfDouble: IAggregate{
      double value;
      bool hasValue;
      public void Add(double value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public double GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfDecimal: IAggregate{
      decimal value;
      bool hasValue;
      public void Add(decimal value){
        if (!this.hasValue){
          this.value = value;
          this.hasValue = true;
        }
        if (value > this.value)
          this.value = value;
      }
      public decimal GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return 0;
      }
    }
    public struct MaxOfString: IAggregate{
      string value;
      public void Add(string value){
        if (value != null){
          if (this.value == null || value.CompareTo(this.value) > 0)
            this.value = value;
        }
      }
      public string GetValue(){
        string result = this.value;
        this.value = null;
        return result;
      }
    }
    public struct MaxOfDateTime: IAggregate{
      DateTime value;
      bool hasValue;
      public void Add(DateTime value){
        if (!this.hasValue || value > this.value){
          this.value = value;
          this.hasValue = true;
        }
      }
      public DateTime GetValue(){
        DateTime result = this.value;
        this.value = new DateTime();
        this.hasValue = false;
        return result;
      }
    }
    public struct MaxOfSqlByte: IAggregate{
      byte value;
      bool hasValue;
      public void Add(SqlByte value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (byte)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (byte)value;
        }
      }
      public SqlByte GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlByte.Null;
      }
    }
    public struct MaxOfSqlInt16: IAggregate{
      short value;
      bool hasValue;
      public void Add(SqlInt16 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (short)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (short)value;
        }
      }
      public SqlInt16 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt16.Null;
      }
    }
    public struct MaxOfSqlInt32: IAggregate{
      int value;
      bool hasValue;
      public void Add(SqlInt32 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (int)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (int)value;
        }
      }
      public SqlInt32 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt32.Null;
      }
    }
    public struct MaxOfSqlInt64: IAggregate{
      long value;
      bool hasValue;
      public void Add(SqlInt64 value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (long)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (long)value;
        }
      }
      public SqlInt64 GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlInt64.Null;
      }
    }
    public struct MaxOfSqlSingle: IAggregate{
      float value;
      bool hasValue;
      public void Add(SqlSingle value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value.Value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = value.Value;
        }
      }
      public SqlSingle GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlSingle.Null;
      }
    }
    public struct MaxOfSqlDouble: IAggregate{
      double value;
      bool hasValue;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = (double)value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = (double)value;
        }
      }
      public SqlDouble GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDouble.Null;
      }
    }
    public struct MaxOfSqlDecimal: IAggregate{
      SqlDecimal value;
      bool hasValue;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = value;
        }
      }
      public SqlDecimal GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDecimal.Null;
      }
    }
    public struct MaxOfSqlMoney: IAggregate{
      SqlMoney value;
      bool hasValue;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (!this.hasValue){
            this.value = value;
            this.hasValue = true;
          }
          if (value > this.value)
            this.value = value;
        }
      }
      public SqlMoney GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlMoney.Null;
      }
    }
    public struct MaxOfSqlString: IAggregate{
      SqlString value;
      bool hasValue;
      public void Add(SqlString value){
        if (!value.IsNull){
          if (!this.hasValue || (bool)SqlString.GreaterThan(value, this.value)){
            this.value = value;
            this.hasValue = true;
          }
        }
      }
      public SqlString GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlString.Null;
      }
    }
    public struct MaxOfSqlDateTime: IAggregate{
      SqlDateTime value;
      bool hasValue;
      public void Add(SqlDateTime value){
        if (!value.IsNull){
          if (!this.hasValue || (bool)SqlDateTime.GreaterThan(value, this.value)){
            this.value = value;
            this.hasValue = true;
          }
        }
      }
      public SqlDateTime GetValue(){
        if (this.hasValue){
          this.hasValue = false;
          return this.value;
        }
        return SqlDateTime.Null;
      }
    }
  }
  public class Sum: IAggregateGroup{
    public struct SumOfInt32: IAggregate{
      int total;
      public void Add(int value){
        this.total = this.total + value;
      }
      public int GetValue(){
        int ret = this.total;
        this.total = 0;
        return ret;
      }
    }
    public struct SumOfInt64: IAggregate{
      long total;
      public void Add(long value){
        this.total = this.total + value;
      }
      public long GetValue(){
        long ret = this.total;
        this.total = 0;
        return ret;
      }
    }
    public struct SumOfDouble: IAggregate{
      double total;
      public void Add(double value){
        this.total = this.total + value;
      }
      public double GetValue(){
        double ret = this.total;
        this.total = 0.0;
        return ret;
      }
    }
    public struct SumOfDecimal: IAggregate{
      decimal total;
      public void Add(decimal value){
        this.total = this.total + value;
      }
      public decimal GetValue(){
        decimal ret = this.total;
        this.total = 0;
        return ret;
      }
    }
    public struct SumOfSqlInt32: IAggregate{
      int total;
      bool hasValue;
      public void Add(SqlInt32 value){
        if (!value.IsNull){
          if (this.hasValue)
            this.total = this.total + (int) value;
          else{
            this.total = (int) value;
            this.hasValue = true;
          }
        }
      }
      public SqlInt32 GetValue(){
        if (!this.hasValue){
          return SqlInt32.Null;
        }
        this.hasValue = false;
        return (SqlInt32) this.total;
      }
    }
    public struct SumOfSqlInt64: IAggregate{
      long total;
      bool hasValue;
      public void Add(SqlInt64 value){
        if (!value.IsNull){
          if (this.hasValue)
            this.total = this.total + (long) value;
          else{
            this.total = (long) value;
            this.hasValue = true;
          }
        }
      }
      public SqlInt64 GetValue(){
        if (!this.hasValue) return SqlInt64.Null;
        this.hasValue = false;
        return (SqlInt64) this.total;
      }
    }
    public struct SumOfSqlDouble: IAggregate{
      SqlDouble total;
      bool hasValue;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          if (this.hasValue){
            this.total = this.total + value;
          }else{
            this.total = value;
            this.hasValue = true;
          }
        }
      }
      public SqlDouble GetValue(){
        if (!this.hasValue) return SqlDouble.Null;
        this.hasValue = false;
        return this.total;
      }
    }
    public struct SumOfSqlDecimal: IAggregate{
      SqlDecimal total;
      bool hasValue;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (this.hasValue)
            this.total = this.total + value;
          else{
            this.total = value;
            this.hasValue = true;
          }
        }
      }
      public SqlDecimal GetValue(){
        if (!this.hasValue) return SqlDecimal.Null;
        this.hasValue = false;
        return this.total;
      }
    }
    public struct SumOfSqlMoney: IAggregate{
      SqlMoney total;
      bool hasValue;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (this.hasValue)
            this.total = this.total + value;
          else{
            this.total = value;
            this.hasValue = true;
          }
        }
      }
      public SqlMoney GetValue(){
        if (!this.hasValue) return SqlMoney.Null;
        this.hasValue = false;
        return this.total;
      }
    }
  }
  public class Avg: IAggregateGroup{
    public struct AvgOfInt32: IAggregate{
      long total;
      long count;
      public void Add(int value){
        this.total += value;
        this.count++;
      }
      public int GetValue(){
        int result = (int)(this.total / this.count);
        this.total = 0;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfInt64: IAggregate{
      decimal total;
      long count;
      public void Add(long value){
        this.total += value;
        this.count++;
      }
      public long GetValue(){
        long result = (long)(this.total / this.count);
        this.total = 0;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfDouble: IAggregate{
      double total;
      long count;
      public void Add(double value){
        this.total += value;
        this.count++;
      }
      public double GetValue(){
        double result = this.total / this.count;
        this.total = 0;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfDecimal: IAggregate{
      decimal total;
      long count;
      public void Add(decimal value){
        this.total += value;
        this.count++;
      }
      public decimal GetValue(){
        decimal result = this.total / this.count;
        this.total = 0;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlInt32: IAggregate{
      long total;
      long count;
      public void Add(SqlInt32 value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = (int)value;
          else
            this.total += (int)value;
          this.count++;
        }
      }
      public SqlInt32 GetValue(){
        if (this.count == 0) return SqlInt32.Null;
        int result = (int)(this.total / this.count);
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlInt64: IAggregate{
      decimal total;
      long count;
      public void Add(SqlInt64 value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = (long)value;
          else
            this.total += (long)value;
          this.count++;
        }
      }
      public SqlInt64 GetValue(){
        if (this.count == 0) return SqlInt64.Null;
        long result = (long)(this.total / this.count);
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlDouble: IAggregate{
      SqlDouble total;
      long count;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = value;
          else
            this.total += value;
          this.count++;
        }
      }
      public SqlDouble GetValue(){
        if (this.count == 0) return SqlDouble.Null;
        SqlDouble result = this.total / count;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlDecimal: IAggregate{
      SqlDecimal total;
      long count;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = value;
          else
            this.total += value;
          this.count++;
        }
      }
      public SqlDecimal GetValue(){
        if (this.count == 0) return SqlDecimal.Null;
        SqlDecimal result = this.total / count;
        this.count = 0;
        return result;
      }
    }
    public struct AvgOfSqlMoney: IAggregate{
      SqlMoney total;
      long count;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (this.count == 0)
            this.total = value;
          else
            this.total += value;
          this.count++;
        }
      }
      public SqlMoney GetValue(){
        if (this.count == 0) return SqlMoney.Null;
        SqlMoney result = this.total / count;
        this.count = 0;
        return result;
      }
    }
  }
  public class Stdev: IAggregateGroup{
    public struct StdevOfDouble: IAggregate{
      double sumX;
      double sumX2;
      int count;
      public void Add(double value){
        this.sumX += value;
        this.sumX2 += (value * value);
        this.count++;
      }
      public double GetValue(){
        int c = count - 1;
        double result = Math.Sqrt((sumX2/c) - ((sumX * sumX)/count/c));
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return result;
      }
    }
    public struct StdevOfDecimal: IAggregate{
      decimal sumX;
      decimal sumX2;
      int count;
      public void Add(decimal value){
        this.sumX += value;
        this.sumX2 += (value * value);
        this.count++;
      }
      public double GetValue(){
        int c = count - 1;
        // note: using Math.Sqrt(double) would lose precision, so use SqlDecimal.Power
        SqlDecimal result = SqlDecimal.Power((sumX2/c) - ((sumX * sumX)/count/c), 0.5);
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return (double)(SqlDouble)result;
      }
    }
    public struct StdevOfSqlDouble: IAggregate{
      double sumX;
      double sumX2;
      int count;
      public void Add(SqlDouble value){
        if (!value.IsNull){
          double dv = (double) value;
          this.sumX += dv;
          this.sumX2 += dv * dv;
          this.count++;
        }
      }
      public SqlDouble GetValue(){
        if (this.count < 2) return SqlDouble.Null;
        int c = count - 1;
        double result = Math.Sqrt((sumX2/c) - ((sumX * sumX)/count/c));
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return (SqlDouble) result;
      }
    }
    public struct StdevOfSqlDecimal: IAggregate{
      SqlDecimal sumX;
      SqlDecimal sumX2;
      int count;
      public void Add(SqlDecimal value){
        if (!value.IsNull){
          if (this.count == 0){
            this.sumX = value;
            this.sumX2 = value * value;
          }else{
            this.sumX += value;
            this.sumX2 += value * value;
          }
          this.count++;
        }
      }
      public SqlDouble GetValue(){
        if (this.count < 2) return SqlDecimal.Null;
        int c = count - 1;
        SqlDecimal result = SqlDecimal.Power((sumX2/c) - ((sumX * sumX)/count/c), 0.5);
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return (SqlDouble)result;
      }
    }
    public struct StdevOfSqlMoney: IAggregate{
      SqlMoney sumX;
      SqlMoney sumX2;
      int count;
      public void Add(SqlMoney value){
        if (!value.IsNull){
          if (this.count == 0){
            this.sumX = value;
            this.sumX2 = value * value;
          }else{
            this.sumX += value;
            this.sumX2 += value * value;
          }
          this.count++;
        }
      }
      public SqlDouble GetValue(){
        if (this.count < 2) return SqlMoney.Null;
        int c = count - 1;
        SqlDecimal result = SqlDecimal.Power((sumX2/c) - ((sumX * sumX)/count/c), 0.5);
        this.sumX = 0;
        this.sumX2 = 0;
        this.count = 0;
        return (SqlDouble)result;
      }
    }
  }
  public class Count: IAggregateGroup{
    public struct CountOfObject: IAggregate{
      int count;
      public void Add(object value){
        count++;
      }
      public int GetValue(){
        int result = count;
        this.count = 0;
        return result;
      }
    }
  }

  [Anonymous]
  public sealed class SqlFunctions{
    public static SqlByte Abs(SqlByte value){
      return value;
    }
    public static SqlInt16 Abs(SqlInt16 value){
      if (value.IsNull) return SqlInt16.Null;
      return Math.Abs((short)value);
    }
    public static SqlInt32 Abs(SqlInt32 value){
      if (value.IsNull) return SqlInt32.Null;
      return Math.Abs((int)value);
    }
    public static SqlInt64 Abs(SqlInt64 value){
      if (value.IsNull) return SqlInt64.Null;
      return Math.Abs((long)value);
    }
    public static SqlDouble Abs(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Abs((double)value);
    }
    public static SqlDecimal Abs(SqlDecimal value){
      if (value.IsNull) return SqlDecimal.Null;
      return (value < 0) ? -value : value;
    }
    public static SqlMoney Abs(SqlMoney value){
      if (value.IsNull) return SqlMoney.Null;
      return (value < 0) ? -value : value;
    }
    public static SqlDouble Acos(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Acos((double)value);
    }
    public static SqlDouble Asin(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Asin((double)value);
    }
    public static SqlDouble Atan(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Atan((double)value);
    }
    public static SqlDouble Atn2(SqlDouble value1, SqlDouble value2){
      if (value1.IsNull || value2.IsNull) return SqlDouble.Null;
      return Math.Atan2((double)value1, (double)value2);
    }
    public static SqlByte Ceiling(SqlByte value){
      return value;
    }
    public static SqlInt16 Ceiling(SqlInt16 value){
      return value;
    }
    public static SqlInt32 Ceiling(SqlInt32 value){
      return value;
    }
    public static SqlInt64 Ceiling(SqlInt64 value){
      return value;
    }
    public static SqlDouble Ceiling(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Ceiling((double)value);
    }
    public static SqlDecimal Ceiling(SqlDecimal value){
      return SqlDecimal.Ceiling(value);
    }
    public static SqlMoney Ceiling(SqlMoney value){
      return (SqlMoney)SqlDecimal.Ceiling(value);
    }
    public static SqlInt32 CharIndex(SqlString pattern, SqlString source){
      if (pattern.IsNull || source.IsNull) return SqlInt32.Null;
      return ((string)source).IndexOf((string)pattern) + 1;
    }
    public static SqlDouble Cos(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Cos((double)value);
    }
    public static SqlDateTime DateAdd(SqlDatePart part, SqlInt32 value, SqlDateTime date){
      if (value.IsNull || date.IsNull) return SqlDateTime.Null;
      int incr = (int)value;
      DateTime dt = (DateTime)date;
      switch (part){
        case SqlDatePart.Year:
          return dt.AddYears(incr);
        case SqlDatePart.Month:
          return dt.AddMonths(incr);
        case SqlDatePart.Day:
          return dt.AddDays(incr);
        case SqlDatePart.Hour:
          return dt.AddHours(incr);
        case SqlDatePart.Minute:
          return dt.AddMinutes(incr);
        case SqlDatePart.Second:
          return dt.AddSeconds(incr);
        case SqlDatePart.Millisecond:
          return dt.AddMilliseconds(incr);
      }
      return dt;
    }
    public static SqlInt32 DatePart(SqlDatePart part, SqlDateTime date){
      if (date.IsNull) return SqlInt32.Null;
      DateTime dt = (DateTime)date;
      switch (part){
        case SqlDatePart.Year: 
          return dt.Year;
        case SqlDatePart.Month:
          return dt.Month;
        case SqlDatePart.Week:
          return (dt.DayOfYear + 6)/ 7;
        case SqlDatePart.WeekDay:
          return (int)dt.DayOfWeek;
        case SqlDatePart.Day:
          return dt.Day;
        case SqlDatePart.DayOfYear:
          return dt.DayOfYear;
        case SqlDatePart.Hour:
          return dt.Hour;
        case SqlDatePart.Minute:
          return dt.Minute;
        case SqlDatePart.Second:
          return dt.Second;
        case SqlDatePart.Millisecond:
          return dt.Millisecond;
      }
      return 0;
    }
    public static SqlDouble Degrees(SqlDouble radians){
      if (radians.IsNull) return SqlDouble.Null;
      return ((double)radians) * Math.PI / 2;
    }
    public static SqlDouble Exp(SqlDouble exponent){
      return Math.Exp((double)exponent);
    }
    public static SqlByte Floor(SqlByte value){
      return value;
    }
    public static SqlInt16 Floor(SqlInt16 value){
      return value;
    }
    public static SqlInt32 Floor(SqlInt32 value){
      return value;
    }
    public static SqlInt64 Floor(SqlInt64 value){
      return value;
    }
    public static SqlDouble Floor(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Floor((double)value);
    }
    public static SqlDecimal Floor(SqlDecimal value){
      return SqlDecimal.Floor(value);
    }
    public static SqlMoney Floor(SqlMoney value){
      return (SqlMoney)SqlDecimal.Floor(value);
    }
    public static SqlDateTime GetDate(){
      return DateTime.Now;
    }
    public static SqlDateTime GetUtcDate(){
      return DateTime.UtcNow;
    }
    public static SqlBoolean IsDate(SqlString value){
      if (value.IsNull) return SqlBoolean.Null;
      try{ DateTime.Parse((string)value); }
      catch{ return false; }
      return true;
    }
    public static SqlString Left(SqlString value, SqlInt32 length){
      if (value.IsNull || length.IsNull) return SqlString.Null;
      int len = (int)length;
      string str = (string)value;
      return str.Substring(0, len);
    }
    public static SqlInt32 Len(SqlString value){
      if (value.IsNull) return SqlInt32.Null;
      return ((string)value).Length;
    }
    public static SqlDouble Log(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Log((double)value);
    }
    public static SqlDouble Log10(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Log10((double)value);
    }
    public static SqlDouble Power(SqlDouble value, SqlDouble exponent){
      if (value.IsNull || exponent.IsNull) return SqlDouble.Null;
      return Math.Pow((double)value, (double)exponent);
    }
    public static SqlString Replace(SqlString source, SqlString oldValue, SqlString newValue){
      if (source.IsNull || oldValue.IsNull || newValue.IsNull) return SqlString.Null;
      return ((string)source).Replace((string)oldValue, (string)newValue);
    }
    public static SqlString Reverse(SqlString value){
      if (value.IsNull) return SqlString.Null;
      string str = (string)value;
      StringBuilder sb = new StringBuilder(str.Length);
      for(int i = str.Length - 1; i >= 0; i--)
        sb.Append(str[i]);       
      return sb.ToString();
    }
    public static SqlString Right(SqlString value, SqlInt32 length){
      if (value.IsNull || length.IsNull) return SqlString.Null;
      string str = (string)value;
      int len = Math.Min((int)length, str.Length);
      return str.Substring(str.Length - len - 1, len);
    }
    public static SqlDouble Round(SqlDouble value, SqlInt32 precision){
      if (value.IsNull || precision.IsNull) return SqlDouble.Null;
      return Math.Round((double)value, (int)precision);
    }
    public static SqlDecimal Round(SqlDecimal value, SqlInt32 precision){
      if (value.IsNull || precision.IsNull) return SqlDecimal.Null;
      return SqlDecimal.Round(value, (int)precision);
    }
    public static SqlMoney Round(SqlMoney value, SqlInt32 precision){
      if (value.IsNull || precision.IsNull) return SqlMoney.Null;
      return (SqlMoney) SqlDecimal.Round(value, (int)precision);
    }
    public static SqlDouble Sin(SqlDouble value){
      if (value.IsNull) return SqlDouble.Null;
      return Math.Sin((double)value);
    }
    public static SqlString Stuff(SqlString source, SqlInt32 position, SqlInt32 length, SqlString value){
      if (source.IsNull || position.IsNull || length.IsNull) return SqlString.Null;
      int offset = ((int)position) - 1;
      string result = ((string)source).Remove(offset, (int)length);
      if (!value.IsNull) result = result.Insert(offset, (string)value);
      return result;
    }
    public static SqlString Substring(SqlString source, SqlInt32 position, SqlInt32 length){
      if (source.IsNull || position.IsNull || length.IsNull) return SqlString.Null;
      int offset = ((int)position) - 1;
      return ((string)source).Substring(offset, (int)length);
    }
  }

  [Anonymous]
  public enum SqlDatePart{
    Year,
    Quarter,
    Month,
    Day,
    DayOfYear,
    Week,
    WeekDay,
    Hour,
    Minute,
    Second,
    Millisecond
  }

  [Anonymous]
  public enum SqlHint{
    HoldLock,
    Serializable,
    RepeatableRead,
    ReadCommitted,
    ReadUncommitted,
    NoLock, 
    RowLock,
    PageLock,
    TableLock,
    TableLockExclusive,
    ReadPast,
    UpdateLock,
    ExclusiveLock,
  }
}
#endif
#endif
namespace Microsoft.Contracts{

#if CCINamespace
  using Microsoft.Cci;
#else
  using System.Compiler;
#endif

  [Template(typeof(ElementTypeAttribute))]
  public class Range: System.Collections.IEnumerable{
    public int From, To, Step;
    public int FromO, ToO;
    //private bool ok;
    //public Range(int f, int t, int s) {
    //From=f-1; To=t; Step=s; ok = false;
    //}
    public Range(int f, int t) {
      From=f; To=t; Step=1; //ok = false;
    }
    public RangeEnumerator GetEnumerator(){
      return new RangeEnumerator(From, To, Step);
    }
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator(){
      return new RangeEnumerator(From, To, Step);
    }
    
    public struct RangeEnumerator:System.Collections.IEnumerator{
      private int from, to, step;
      private bool ok ;
      public RangeEnumerator(int f, int t, int s) {
        from=f; to=t; step=s; ok = false;
      }
      public object Current{get {if(ok) return from; else throw new Exception("RangeEnumerator.Current: wrong protocol");}}
      public bool MoveNext() {if (!ok) ok = true; else from+=step; return from<=to;}
      public void Reset() {throw new Exception("RangeEnumerator.Reset: not implemented");}
    }
  }

  /// <summary>
  /// Used as an optional modifier on type parameter occurrences to override any non-null
  /// instantiations.
  /// </summary>
  public sealed class NullableType {
  }
  public sealed class NonNullType {
    [Throws("System.NullException")]
    [StateIndependent]
    [System.Diagnostics.DebuggerStepThrough]
    [System.Diagnostics.Conditional("DEBUG")]
    public static void AssertNotNull([Delayed] UIntPtr ptr) {
      if (ptr == (UIntPtr)0) {
#if KERNEL
        Microsoft.Singularity.DebugStub.Break();
#else
        Microsoft.Singularity.V1.Services.DebugService.Break();
#endif
        throw new NullException();
      }
    }
    [Throws("System.NullException")]
    [StateIndependent]
    [System.Diagnostics.DebuggerStepThrough]
    [System.Diagnostics.Conditional("DEBUG")]
    public static void AssertNotNullImplicit([Delayed] UIntPtr ptr) {
      if (ptr == (UIntPtr)0) {
#if KERNEL
        Microsoft.Singularity.DebugStub.Break();
#else
        Microsoft.Singularity.V1.Services.DebugService.Break();
#endif
        throw new NullException();
      }
    }
    [Throws("System.NullException")]
    [StateIndependent]
    [System.Diagnostics.DebuggerStepThrough]
    [System.Diagnostics.Conditional("DEBUG")]
    public static void AssertNotNull([Delayed] object obj) {
      if (obj == null) {
#if KERNEL
        Microsoft.Singularity.DebugStub.Break();
#else
        Microsoft.Singularity.V1.Services.DebugService.Break();
#endif
        throw new NullException();
      }
    }
    [Throws("System.NullException")]
    [StateIndependent]
    [System.Diagnostics.DebuggerStepThrough]
    [System.Diagnostics.Conditional("DEBUG")]
    public static void AssertNotNullImplicit([Delayed] object obj) {
      if (obj == null) {
#if KERNEL
        Microsoft.Singularity.DebugStub.Break();
#else
        Microsoft.Singularity.V1.Services.DebugService.Break();
#endif
        throw new NullException();
      }
    }
  }
  public class AssertHelpers {
    #region Assert methods
    [System.Diagnostics.DebuggerStepThrough]
    public static void Assert(bool b) {
      if (!b)
        throw new Contracts.AssertException();
    }
    [System.Diagnostics.DebuggerStepThrough]
    public static void AssertLoopInvariant(bool b) {
      if (!b)
        throw new Contracts.LoopInvariantException();
    }
    [System.Diagnostics.DebuggerStepThrough]
    public static void Assert(bool b, string s) {
      if (!b)
        throw new Contracts.AssertException(s);
    }
    [System.Diagnostics.DebuggerStepThrough]
    public static void Assert(bool b, string s, Exception inner) {
      if (!b)
        throw new Contracts.AssertException(s,inner);
    }
    /// <summary>
    /// Is deserialized by Boogie.
    /// </summary>
    /// <param name="condition">Serialized condition</param>
    [System.Diagnostics.DebuggerStepThrough]
    [Obsolete("Use the two-argument version instead. Delete this one when the LKG > 7301.")]
    public static void AssertStatement(string condition) {
    }
    /// <summary>
    /// Is deserialized by Boogie.
    /// </summary>
    /// <param name="condition">Serialized condition</param>
    /// <param name="messageForUser">Text to use in error messages</param>
    [System.Diagnostics.DebuggerStepThrough]
    public static void AssertStatement(string condition, string messageForUser) {
    }
    /// <summary>
    /// Is deserialized by Boogie.
    /// </summary>
    /// <param name="condition">Serialized condition</param>
    [System.Diagnostics.DebuggerStepThrough]
    [Obsolete("Use the two-argument version instead. Delete this one when the LKG > 7301.")]
    public static void LoopInvariant(string condition) {
    }
    /// <summary>
    /// Is deserialized by Boogie.
    /// </summary>
    /// <param name="condition">Serialized condition</param>
    /// <param name="messageForUser">Text to use in error messages</param>
    [System.Diagnostics.DebuggerStepThrough]
    public static void LoopInvariant(string condition, string messageForUser) {
    }
    #endregion Assert methods
    #region Assume methods
    [System.Diagnostics.DebuggerStepThrough]
    public static void Assume(bool b) {
      if (!b)
        throw new Contracts.AssumeException();
    }
    [System.Diagnostics.DebuggerStepThrough]
    public static void Assume(bool b, string s) {
      if (!b)
        throw new Contracts.AssumeException(s);
    }
    [System.Diagnostics.DebuggerStepThrough]
    public static void Assume(bool b, string s, Exception inner) {
      if (!b)
        throw new Contracts.AssumeException(s,inner);
    }
    /// <summary>
    /// Is deserialized by Boogie.
    /// </summary>
    /// <param name="condition">Serialized condition</param>
    [System.Diagnostics.DebuggerStepThrough]
    public static void AssumeStatement(string condition) {
    }
    #endregion Assume methods
    [return: Microsoft.Contracts.NotNull]
    public static object OwnerIs(object owner, [Microsoft.Contracts.NotNull] object owned_object) { return owned_object; }
  }
  #region Exceptions
  //---------------------------------------------------------------------------
  //Exceptions
  //---------------------------------------------------------------------------

  public class NoChoiceException : Exception {}
  public class IllegalUpcastException : Exception {}

  public interface ICheckedException {}
  public class CheckedException: Exception, ICheckedException {}

  /// <summary>
  /// The Spec# compiler emits "throw new UnreachableException();" statements in places that it knows are unreachable, but that are considered reachable by the CLR verifier.
  /// </summary>
  public class UnreachableException : Exception {
    public UnreachableException() { }
    public UnreachableException(string s) : base(s) { }
    public UnreachableException(string s, Exception inner) : base(s, inner) { }
  }
  public class ContractException : Exception {
    public ContractException() {}
    public ContractException(string s) : base(s) {}
    public ContractException(string s, Exception inner) : base(s,inner) {}
  }
  public class AssertException : ContractException {
    public AssertException() {}
    public AssertException(string s) : base(s) {}
    public AssertException(string s, Exception inner) : base(s,inner) {}
  }
  public class LoopInvariantException : AssertException {
    public LoopInvariantException() {}
    public LoopInvariantException(string s) : base(s) {}
    public LoopInvariantException(string s, Exception inner) : base(s,inner) {}
  }
  public class AssumeException : ContractException {
    public AssumeException() {}
    public AssumeException(string s) : base(s) {}
    public AssumeException(string s, Exception inner) : base(s,inner) {}
  }
  /// <summary>
  /// Thrown when evaluation of a contract clause throws an exception.
  /// </summary>
  public class InvalidContractException : ContractException {
    public InvalidContractException() {}
    public InvalidContractException(string s) : base(s) {}
    public InvalidContractException(string s, Exception inner) : base(s,inner) {}
  }
  public class RequiresException : ContractException {
    public RequiresException() {}
    public RequiresException(string s) : base(s) {}
    public RequiresException(string s, Exception inner) : base(s,inner) {}
  }
  public class EnsuresException : ContractException {
    public EnsuresException() {}
    public EnsuresException(string s) : base(s) {}
    public EnsuresException(string s, Exception inner) : base(s,inner) {}
  }
  public class ModifiesException : ContractException {
    public ModifiesException() {}
    public ModifiesException(string s) : base(s) {}
    public ModifiesException(string s, Exception inner) : base(s,inner) {}
  }
  public class ThrowsException : ContractException {
    public ThrowsException() {}
    public ThrowsException(string s) : base(s) {}
    public ThrowsException(string s, Exception inner) : base(s,inner) {}
  }
  public class DoesException : ContractException {
    public DoesException() {}
    public DoesException(string s) : base(s) {}
    public DoesException(string s, Exception inner) : base(s,inner) {}
  }
  public class InvariantException : ContractException {
    public InvariantException() {}
    public InvariantException(string s) : base(s) {}
    public InvariantException(string s, Exception inner) : base(s,inner) {}
  }
  public class NullException : ContractException {
    public NullException() {}
    public NullException(string s) : base(s) {}
    public NullException(string s, Exception inner) : base(s,inner) {}
  }
  public class ContractMarkerException : ContractException {
  }
  #endregion Exceptions
  #region Attributes
  //---------------------------------------------------------------------------
  //Attributes
  //---------------------------------------------------------------------------
  internal sealed class SpecTargets{
    internal const AttributeTargets Code = 
      AttributeTargets.Constructor|AttributeTargets.Method|AttributeTargets.Property|AttributeTargets.Event|AttributeTargets.Delegate;
    internal const AttributeTargets Containers = 
      AttributeTargets.Struct|AttributeTargets.Class|AttributeTargets.Interface;
    internal const AttributeTargets CodeAndTheirContainers =
      Code|Containers;
    internal const AttributeTargets 
      CodeFieldsAndTheirContainers = CodeAndTheirContainers|AttributeTargets.Field;
  }
  /// <summary>
  /// We serialize constructs like Requires as custom attributes. But then there
  /// is the problem of how to serialize custom attributes that have been put onto
  /// such constructs. Since nested attributes are not allowed, we encode them
  /// by serializing the nested attributes and then emitting an attribute of type
  /// NestedAttributeCount with the number of nested attributes. That way, upon
  /// deserialization, as long as the order of the serialized attributes can be
  /// depended upon, we can reconstitute the nested attributes.
  /// So the Spec# source:
  /// "[A][B] requires P"
  /// would be serialized as
  /// "A(...), B(...), NestedAttributeCount(2), Requires(P,...)".
  /// </summary>
 /*
  [AttributeUsage(AttributeTargets.All,AllowMultiple=true, Inherited = true)]
  public class NestedAttributeCount : Attribute{
    public int numberOfNestedAttributes;
    public NestedAttributeCount(int _numberOfNestedAttributes){
      numberOfNestedAttributes = _numberOfNestedAttributes;
    }
  }
  */
  public class AttributeWithContext : Attribute{
    public string Filename = "<unknown>";
    public int StartLine = 0;
    public int StartColumn = 0;
    public int EndLine = 0;
    public int EndColumn = 0;
    public string SourceText = "";
    public AttributeWithContext(){}
    public AttributeWithContext(string filename, int startline, int startcol, int endline, int endcol)
    : this(filename, startline, startcol, endline, endcol, "")
    {}
    public AttributeWithContext(string filename, int startline, int startcol, int endline, int endcol, string sourceText){
      this.Filename = filename;
      this.StartLine = startline;
      this.StartColumn = startcol;
      this.EndLine = endline;
      this.EndColumn = endcol;
      this.SourceText = sourceText;
    }
  }
  [AttributeUsage(Microsoft.Contracts.SpecTargets.Code, AllowMultiple=false, Inherited = true)]
  public sealed class PureAttribute: Microsoft.Contracts.AttributeWithContext{
  }
  /*Diego's Attributes */
  [AttributeUsage(AttributeTargets.Field, AllowMultiple = false, Inherited = false)]
  public sealed class OnceAttribute : AttributeWithContext
  {
  }
  [AttributeUsage(SpecTargets.Code,AllowMultiple=false, Inherited = true)]
  public sealed class WriteConfinedAttribute: AttributeWithContext{
  }
    [AttributeUsage(SpecTargets.Code,AllowMultiple=false, Inherited = true)]
  public sealed class GlobalWriteAttribute: AttributeWithContext{
      public bool Value;
      GlobalWriteAttribute()
      {
          Value = true;
      }
      GlobalWriteAttribute(bool value)
      {
          this.Value = value;
      }

  }
    [AttributeUsage(SpecTargets.Code,AllowMultiple=false, Inherited = true)]
  public sealed class GlobalReadAttribute: AttributeWithContext{
      public bool Value;
      GlobalReadAttribute()
      {
          Value = true;
      }
      GlobalReadAttribute(bool value)
      {
          this.Value = value;
      }

  }
    [AttributeUsage(SpecTargets.Code, AllowMultiple = false, Inherited = true)]
    public sealed class GlobalAccessAttribute : AttributeWithContext
    {
        public bool Value;
        GlobalAccessAttribute()
        {
            Value = true;
        }
        GlobalAccessAttribute(bool value)
        {
            this.Value = value;
        }

    }
    [AttributeUsage(SpecTargets.Code | AttributeTargets.ReturnValue | AttributeTargets.Field | AttributeTargets.Parameter, AllowMultiple = true, Inherited = true)]
  public sealed class FreshAttribute: AttributeWithContext{
  }
    [AttributeUsage(SpecTargets.Code | AttributeTargets.Parameter, AllowMultiple = true, Inherited = true)]
  public sealed class EscapesAttribute: AttributeWithContext{
      public bool Value;
      public bool Owned;
      public EscapesAttribute()
      {
          Value = false;
          Owned = false;
      }
      public EscapesAttribute(bool value)
      {
          this.Value = value;
          this.Owned = true;
      }
    public EscapesAttribute(bool value, bool own) {
      this.Value = value;
      this.Owned = own;
    }
  }
    /**/

  [AttributeUsage(SpecTargets.Code,AllowMultiple=false, Inherited = true)]
  public sealed class StateIndependentAttribute: AttributeWithContext{
  }
  [AttributeUsage(AttributeTargets.ReturnValue|AttributeTargets.Field|AttributeTargets.Parameter,AllowMultiple=true, Inherited = false)]
  public sealed class NotNullAttribute: AttributeWithContext{
  }
  [AttributeUsage(AttributeTargets.Method | AttributeTargets.Constructor | AttributeTargets.Parameter, AllowMultiple = false, Inherited = true)]
  public sealed class DelayedAttribute : AttributeWithContext {
  }
  [AttributeUsage(AttributeTargets.Constructor, AllowMultiple = false)]
  public sealed class NotDelayedAttribute : AttributeWithContext {
  }
  
  [AttributeUsage(SpecTargets.Containers, AllowMultiple = false, Inherited = false)]
  public sealed class NotNullGenericArgumentsAttribute : AttributeWithContext {
    public string PositionOfNotNulls;
    public NotNullGenericArgumentsAttribute(string positionOfNotNulls) {
      PositionOfNotNulls = positionOfNotNulls;
    }
  }
  [AttributeUsage(SpecTargets.CodeFieldsAndTheirContainers, AllowMultiple = false, Inherited = false)]
  public sealed class EncodedTypeSpecAttribute : AttributeWithContext {
    public int token;
    public EncodedTypeSpecAttribute(int token) {
      this.token = token;
    }
  }
  [AttributeUsage(AttributeTargets.Field)]
  public sealed class StrictReadonlyAttribute: Attribute{
  }
  [AttributeUsage(SpecTargets.CodeFieldsAndTheirContainers,AllowMultiple=false, Inherited = true)]
  public sealed class ModelAttribute: AttributeWithContext{
  }
  [AttributeUsage(SpecTargets.CodeFieldsAndTheirContainers,AllowMultiple=false, Inherited = true)]
  public sealed class SpecPublicAttribute: AttributeWithContext{
  }
  [AttributeUsage(SpecTargets.CodeFieldsAndTheirContainers,AllowMultiple=false, Inherited = true)]
  public sealed class SpecProtectedAttribute: AttributeWithContext{
  }
  [AttributeUsage(SpecTargets.CodeFieldsAndTheirContainers,AllowMultiple=false, Inherited = true)]
  public sealed class SpecInternalAttribute: AttributeWithContext{
  }

  /// <summary>
  /// Used to mark the beginning of contracts so that static verification can recognize them
  /// (either to ignore them or to treat them specially)
  /// </summary>
  public sealed class ContractMarkers {
    public static void BeginRequires() { }
    public static void EndRequires() { }
  }
  [AttributeUsage(SpecTargets.Code,AllowMultiple=true, Inherited = true)]
  public sealed class RequiresAttribute: AttributeWithContext{
    public string Requires;
    public RequiresAttribute(string _requires){
      Requires = _requires;
    }
    public RequiresAttribute(string _requires, string filename, int startline, int startcol, int endline, int endcol)
      : base(filename,startline,startcol,endline,endcol){
      Requires = _requires;
    }
    public RequiresAttribute(string _requires, string filename, int startline, int startcol, int endline, int endcol, string sourceText)
      : base(filename,startline,startcol,endline,endcol,sourceText){
      Requires = _requires;
    }
  }
  [AttributeUsage(SpecTargets.Code,AllowMultiple=true, Inherited = true)]
  public sealed class EnsuresAttribute: AttributeWithContext{
    public string Ensures;
    public EnsuresAttribute(string _ensures) {
      Ensures = _ensures;
    }
    public EnsuresAttribute(string _ensures, string filename, int startline, int startcol, int endline, int endcol)
      : base(filename,startline,startcol,endline,endcol){
      Ensures = _ensures;
    }
    public EnsuresAttribute(string _ensures, string filename, int startline, int startcol, int endline, int endcol, string sourceText)
      : base(filename,startline,startcol,endline,endcol,sourceText){
      Ensures = _ensures;
    }
}
  [AttributeUsage(SpecTargets.Code,AllowMultiple=true, Inherited = true)]
  public sealed class ModifiesAttribute: AttributeWithContext{
    public string Modifies;
    public ModifiesAttribute(string _modifies) {
      Modifies = _modifies;
    }
    public ModifiesAttribute(string _modifies, string filename, int startline, int startcol, int endline, int endcol)
      : base(filename,startline,startcol,endline,endcol){
      Modifies = _modifies;
    }
    public ModifiesAttribute(string _modifies, string filename, int startline, int startcol, int endline, int endcol, string sourceText)
      : base(filename,startline,startcol,endline,endcol,sourceText){
      Modifies = _modifies;
    }
  }
  [AttributeUsage(SpecTargets.Code, AllowMultiple = false, Inherited = false)]
  public sealed class HasWitnessAttribute : AttributeWithContext {
  }
  [AttributeUsage(SpecTargets.Code, AllowMultiple = false, Inherited = false)]
  public sealed class InferredReturnValueAttribute : AttributeWithContext {
    public string Value;
    public InferredReturnValueAttribute(string value) {
      this.Value = value;
    }
  }
  [AttributeUsage(SpecTargets.Code,AllowMultiple=true, Inherited = true)]
  public sealed class ThrowsAttribute: AttributeWithContext{
    public string Throws;
    public ThrowsAttribute(string _throws) {
      Throws = _throws;
    }
    public ThrowsAttribute(string _throws, string filename, int startline, int startcol, int endline, int endcol)
      : base(filename,startline,startcol,endline,endcol){
      Throws = _throws;
    }
    public ThrowsAttribute(string _throws, string filename, int startline, int startcol, int endline, int endcol, string sourceText)
      : base(filename,startline,startcol,endline,endcol,sourceText){
      Throws = _throws;
    }
  }
  [AttributeUsage(AttributeTargets.Method | AttributeTargets.Property,AllowMultiple=true, Inherited = false)]
  public sealed class DoesAttribute: AttributeWithContext{
    public string Does;
    public DoesAttribute(string _does) {
      Does = _does;
    }
    public DoesAttribute(string _does, string filename, int startline, int startcol, int endline, int endcol)
      : base(filename,startline,startcol,endline,endcol){
      Does = _does;
    }
    public DoesAttribute(string _does, string filename, int startline, int startcol, int endline, int endcol, string sourceText)
      : base(filename,startline,startcol,endline,endcol,sourceText){
      Does = _does;
    }
  }




  [AttributeUsage(SpecTargets.Containers,AllowMultiple=true, Inherited = true)]
  public sealed class InvariantAttribute: AttributeWithContext{
    public string Invariant;
    public InvariantAttribute(string _invariant) {
      Invariant = _invariant;
    }
    public InvariantAttribute(string _invariant, string filename, int startline, int startcol, int endline, int endcol) {
      Invariant = _invariant;
      Filename = filename;
      StartLine = startline;
      StartColumn = startcol;
      EndLine = endline;
      EndColumn = endcol;
    }
  }
  
  [AttributeUsage(AttributeTargets.Assembly, AllowMultiple = false, Inherited = false)]
  public sealed class ShadowsAssemblyAttribute : System.Attribute{
    //TODO: we really want a single argument that provides a complete name and then construct an AssemblyReference from it.
    //TODO: make the Spec# compiler aware of this attribute so that it can check that the argument really is a strong name.
    public string PublicKey;
    public string Version;
    public string Name; 
    public ShadowsAssemblyAttribute(string publicKey, string version, string name) {PublicKey=publicKey; Version=version; Name=name;}
  }
  #endregion Attributes
}

#if CCINamespace
namespace Microsoft.Cci.TypeExtensions {
#else
namespace System.Compiler.TypeExtensions {
#endif
}

#if CCINamespace
namespace Microsoft.Cci {
#else
namespace System.Compiler {
#endif
  /// <summary>
  /// This attribute marks a template parameter T as being instantiable only with unmanaged structs
  /// thereby allowing types such as T* in the generic code.
  /// It needs to be present under Everett and Whidbey, since MSIL 2.0 does not have a way to encode
  /// this AFAIK.
  /// </summary>
  [AttributeUsage(AttributeTargets.Class | AttributeTargets.Interface | AttributeTargets.Struct)]
  public sealed class UnmanagedStructTemplateParameterAttribute : System.Attribute
  {
  }

}

namespace Microsoft.Contracts{
#if CCINamespace
  using Microsoft.Cci;
#endif
  using System.Collections;
  using System.Threading;

  /// <summary>
  /// Called by a <see cref="Guard"/> object to initialize its <i>guard sets</i>.
  /// </summary>
  /// <remarks>
  /// This delegate should not call any methods other than
  /// <see cref="Guard.AddRep"/>,
  /// <see cref="Guard.AddRepObject"/>,
  /// <see cref="Guard.AddImmutableCertificate"/>,
  /// <see cref="Guard.AddObjectImmutableCertificate"/>,
  /// <see cref="Guard.AddLockProtectedCertificate"/>, and
  /// <see cref="Guard.AddObjectLockProtectedCertificate"/>.
  /// </remarks>
  public delegate void InitGuardSetsDelegate();
  // TODO: Remove once the LKG compiler uses CheckInvariantDelegate.
  public delegate bool InvariantHoldsDelegate();
  /// <summary>
  /// Called by a <see cref="Guard"/> object to check that its invariant holds, when it ends writing.
  /// </summary>
  /// <param name="throwException">If true and the invariant does not hold, throws an exception. If false and the invariant does not hold, returns false.</param>
  public delegate bool CheckInvariantDelegate(bool throwException);
  /// <summary>
  /// Called by the <see cref="Guard.AcquireForReading"/> and <see cref="Guard.AcquireForWriting"/> methods
  /// to decide whether to return or to wait.
  /// </summary>
  public delegate bool ThreadConditionDelegate();
  /// <summary>
  /// Called by the <see cref="System.Threading.ThreadStart"/> delegate returned by the
  /// <see cref="Guard.CreateThreadStart"/> method.
  /// </summary>
  public delegate void GuardThreadStart();
  /// <summary>
  /// Delegate that grants access to the frame guards of the objects of a particular type.
  /// </summary>
  /// <param name="o">Object whose frame guard to return</param>
  /// <returns>The frame guard of <paramref name="o"/></returns>
  [return:NotNull]
  public delegate Guard FrameGuardGetter(object o);
  /// <summary>
  /// Thrown by a <see cref="Guard"/> object whenever a race condition, an ownership violation, or an invariant violation is
  /// detected.
  /// </summary>
  public class GuardException : Exception {
    public GuardException() {}
    public GuardException(string message) : base(message) {}
  }

  /// <summary>
  /// Indicates the capability of a thread with respect to a guard (and the resource it protects).
  /// </summary>
  public enum ThreadCapability{
    /// <summary>
    /// The thread cannot access the resource.
    /// </summary>
    None,
    /// <summary>
    /// The thread can read the resource.
    /// </summary>
    Readable,
    /// <summary>
    /// The thread can read and write the resource.
    /// </summary>
    Writable
  }
  /// <summary>
  /// Indicates the activity being performed by a thread on a guard (and the resource it protects).
  /// </summary>
  public enum ThreadActivity{
    /// <summary>
    /// The thread is not acting on the resource.
    /// </summary>
    None,
    /// <summary>
    /// The thread is reading the resource.
    /// </summary>
    Reading,
    /// <summary>
    /// The thread is writing the resource.
    /// </summary>
    Writing
  }
  /// <summary>
  /// Indicates how a thread shares a guard (and the resource it protects).
  /// </summary>
  public enum SharingMode{
    /// <summary>
    /// The thread does not share the resource.
    /// </summary>
    /// <remarks>
    /// Either the object itself is unshared, or the object is shared but not with the thread.
    /// </remarks>
    Unshared,
    /// <summary>
    /// The thread shares the lock-protected resource.
    /// </summary>
    LockProtected,
    /// <summary>
    /// The thread shares the immutable resource.
    /// </summary>
    Immutable
  }
  /// <summary>
  /// Helps guard an object or other resource against race conditions, enforce ownership, and enforce invariants.
  /// </summary>
  public sealed class Guard {
    sealed class Commitment {
      private Guard outer;
      public Guard owner;

      internal Commitment(Guard outer, Guard owner){
        this.outer = outer;
        this.owner = owner;
      }

      public void Release(){
        LocalData locals = outer.Locals;
        outer.owner = null;
        locals.Capability = ThreadCapability.Writable;
        outer = null;
      }
    }
    sealed class RepFrame{
      public Guard/*!*/ frame;
      public Commitment commitment;

      public RepFrame(Guard/*!*/ frame) {
        this.frame = frame;
        //^ base();
      }

      public void Commit(Guard/*!*/ owner) {
        commitment = frame.Commit(owner);
      }

      public void Release(){
        commitment.Release();
        commitment = null;
      }
    }

    sealed class LocalData {
      public SharingMode SharingMode;
      public ThreadCapability Capability;
      public ThreadActivity Activity;
      public override string ToString() {
        return "<" + this.SharingMode.ToString() + "," + this.Capability.ToString() + "," + this.Activity.ToString() + ">";
      }

    }

    sealed class Scheduler {
      bool writerActive;
      int activeReaderCount;
      QueueEntry nextWriter;
      /// <summary>
      /// The queue of entries that will be re-evaluated after the next ReleaseForWriting.
      /// </summary>
      Queue queue = new Queue();

      // invariant writerActive ==> (activeReaderCount == 0 && nextWriter == null);
      // invariant (!writerActive && nextWriter != null) ==> activeReaderCount != 0;
      // The following invariants assume that IsEnabled changes only when writerActive.
      // invariant nextWriter != null ==> nextWriter.IsEnabled; 
      // invariant (!writerActive && nextWriter == null) ==> forall(QueueEntry e in queue; !e.IsReader ==> !e.IsEnabled);

      sealed class QueueEntry {
        public readonly bool IsReader;
        readonly ThreadConditionDelegate condition;
        bool runnable;

        public QueueEntry(bool reader, ThreadConditionDelegate condition){
          this.IsReader = reader;
          this.condition = condition;
        }

        public bool IsEnabled {
          get {
            return condition == null || condition();
          }
        }

        public void Run(){
          lock (this){
            runnable = true;
            Monitor.Pulse(this);
          }
        }

        public void Wait(){
          lock (this){
            while (!runnable)
              Monitor.Wait(this);
          }
        }
      }

      public void AcquireForReading(ThreadConditionDelegate condition){
        QueueEntry entry = new QueueEntry(true, condition);
        lock (this){
          if (writerActive || nextWriter != null || !entry.IsEnabled){
            // This reader will get a chance after the next ReleaseForWriting
            queue.Enqueue(entry);
          } else {
            activeReaderCount++;
            entry.Run();
          }
        }
        entry.Wait();
      }

      public void AcquireForWriting(ThreadConditionDelegate condition){
        QueueEntry entry = new QueueEntry(false, condition);
        lock (this){
          if (writerActive || nextWriter != null || !entry.IsEnabled){
            // This writer will get a chance after the next ReleaseForWriting
            queue.Enqueue(entry);
          } else if (activeReaderCount == 0){
            writerActive = true;
            entry.Run();
          } else {
            nextWriter = entry;
          }
        }
        entry.Wait();
      }

      public void ReleaseForReading(){
        lock (this){
          activeReaderCount--;
          if (activeReaderCount == 0 && nextWriter != null){
            nextWriter.Run();
            writerActive = true;
            nextWriter = null;
          }
        }
      }

      public void ReleaseForWriting(){
        lock (this){
          writerActive = false;
          Queue newQueue = new Queue();
          while (queue.Count > 0){
            QueueEntry entry = (QueueEntry/*!*/)queue.Dequeue();
            if (entry.IsReader && entry.IsEnabled){
              activeReaderCount++;
              entry.Run();
            } else if (!entry.IsReader && nextWriter == null && entry.IsEnabled){
              nextWriter = entry;
            } else {
              newQueue.Enqueue(entry);
            }
          }
          queue = newQueue;
          if (activeReaderCount == 0 && nextWriter != null){
            nextWriter.Run();
            writerActive = true;
            nextWriter = null;
          }
        }
      }
    }

    readonly InitGuardSetsDelegate initFrameSets;
    readonly CheckInvariantDelegate checkInvariant;
    Scheduler scheduler;
    readonly Hashtable/*!*/ repFrames = new Hashtable();
    readonly Hashtable/*!*/ sharedFrames = new Hashtable();
    /// <summary>
    /// Thread-local data indicating the sharing mode, the capability and the activity of the current thread with respect
    /// to this object.
    /// </summary>
    readonly LocalDataStoreSlot localData = Thread.AllocateDataSlot();
    object owner;

    class InvariantHoldsAdaptor{
      InvariantHoldsDelegate invariantHolds;

      public InvariantHoldsAdaptor(InvariantHoldsDelegate invariantHolds){
        this.invariantHolds = invariantHolds;
      }

      public bool CheckInvariant(bool throwException){
        if (!invariantHolds())
          if (throwException)
            throw new Microsoft.Contracts.ObjectInvariantException();
          else
            return false;
        return true;
      }
    }

    // TODO: Remove once the LKG uses the other constructor.
    public Guard([Delayed] InitGuardSetsDelegate initGuardSets, [Delayed] InvariantHoldsDelegate invariantHolds)
      : this(initGuardSets, new CheckInvariantDelegate(new InvariantHoldsAdaptor(invariantHolds).CheckInvariant))
    {
    }

    /// <summary>
    /// Creates a new guard object.
    /// </summary>
    /// <remarks>
    /// Initially, the object is unshared;
    /// the current thread can write and is writing the guard;
    /// and no other thread can access the guard.
    /// </remarks>
    /// <param name="initGuardSets">A delegate that is called to initialize the guard's <i>guard sets</i>.</param>
    /// <param name="checkInvariant">A delegate that is called to check the guard's invariant.</param>
    public Guard([Delayed] InitGuardSetsDelegate initGuardSets, [Delayed] CheckInvariantDelegate checkInvariant){
      this.initFrameSets = initGuardSets;
      this.checkInvariant = checkInvariant;
      LocalData locals = Locals;
      locals.Capability = ThreadCapability.Writable;
      locals.Activity = ThreadActivity.Writing;
    }

    LocalData/*!*/ Locals {
      get {
        LocalData locals;
        object o = Thread.GetData(localData);
        if (o == null) {
          locals = new LocalData();
          Thread.SetData(localData, locals);
        } else
          locals = (LocalData) o;
        return locals;
      }
    }

    /// <summary>
    /// Returns true if the current thread can read the resource; otherwise, returns false.
    /// </summary>
    /// <remarks>
    /// Equivalent to <c>Capability != ThreadCapability.None</c>.
    /// </remarks>
    public bool CanRead {
      get {
        return Locals.Capability != ThreadCapability.None;
      }
    }

    /// <summary>
    /// Returns true if the current thread can write the resource; otherwise, returns false.
    /// </summary>
    /// <remarks>
    /// Equivalent to <c>Capability == ThreadCapability.Writable</c>.
    /// </remarks>
    public bool CanWrite {
      get {
        return Locals.Capability == ThreadCapability.Writable;
      }
    }

    /// <summary>
    /// Returns true if the current thread is reading or writing the resource; otherwise, returns false.
    /// </summary>
    /// <remarks>
    /// Equivalent to <c>Activity != ThreadActivity.None</c>.
    /// </remarks>
    public bool IsActive {
      get {
        return Locals.Activity != ThreadActivity.None;
      }
    }

    public void CheckIsReading(){
      if (Locals.Activity == ThreadActivity.None)
        throw new GuardException("Thread is not reading object.");
    }

    public void CheckIsWriting(){
      if (Locals.Activity != ThreadActivity.Writing)
        throw new GuardException("Thread is not writing object.");
    }

    /// <summary>
    /// Returns the current thread's sharing mode for the resource.
    /// </summary>
    public SharingMode SharingMode {
      get {
        return Locals.SharingMode;
      }
    }

    /// <summary>
    /// Returns the current thread's capability with respect to the resource.
    /// </summary>
    public ThreadCapability Capability {
      get {
        return Locals.Capability;
      }
    }

    /// <summary>
    /// Returns the current thread's activity with respect to the resource.
    /// </summary>
    public ThreadActivity Activity {
      get {
        return Locals.Activity;
      }
    }

    /// <summary>
    /// Starts reading the resource.
    /// </summary>
    public void StartReading(){
      LocalData locals = Locals;
      if (locals.Capability == ThreadCapability.None)
        throw new GuardException("Object is not readable by current thread.");
      if (locals.Activity != ThreadActivity.None)
        throw new GuardException("Thread is already reading or writing object.");
      RegisterSharedFrames();
      locals.Activity = ThreadActivity.Reading;
      foreach (RepFrame repFrame in repFrames.Values)
        repFrame.frame.Locals.Capability = ThreadCapability.Readable;
    }

    /// <summary>
    /// Starts reading the resource; starts reading any transitive owners as necessary.
    /// </summary>
    /// <returns>The furthest transitive owner that was not yet reading.</returns>
    [return:Microsoft.Contracts.NotNull]
    public Guard StartReadingTransitively(){
      Guard rootFrame;
      Commitment commitment = owner as Commitment;
      if (commitment != null)
        rootFrame = commitment.owner.StartReadingTransitively();
      else
        rootFrame = this;
      StartReading();
      return rootFrame;
    }

    /// <summary>
    /// Ends reading the resource.
    /// </summary>
    public void EndReading(){
      EndReading(false);
    }

    /// <summary>
    /// Ends reading the resource; ends reading any transitive owned resources as necessary.
    /// </summary>
    public void EndReadingTransitively(){
      EndReading(true);
    }

    void EndReading(bool transitively){
      LocalData locals = Locals;
      if (locals.Activity != ThreadActivity.Reading)
        throw new GuardException("Thread is not reading object.");
      foreach (RepFrame repFrame in repFrames.Values)
        if (repFrame.frame.Locals.Activity == ThreadActivity.Reading)
          if (transitively)
            repFrame.frame.EndReading(true);
          else
            throw new GuardException("Thread is still reading an owned object.");
      foreach (RepFrame repFrame in repFrames.Values)
        repFrame.frame.Locals.Capability = ThreadCapability.None;
      locals.Activity = ThreadActivity.None;
    }

    /// <summary>
    /// Ends writing the resource.
    /// </summary>
    [Delayed] // This [Delayed] tag isn't actually verifiable, but we believe it does hold here.
    public void EndWriting(){
      EndWriting(false, false);
    }

    [Pure]
    public bool CanStartWriting{
      get {
        LocalData locals = Locals;
        if (locals.Capability != ThreadCapability.Writable)
          return false;
        if (locals.Activity != ThreadActivity.None)
          return false;
        return true;
      }
    }
    [Pure]
    public bool CheckCanStartWriting(){
      LocalData locals = Locals;
      if (locals.Capability != ThreadCapability.Writable)
        throw new GuardException("Object is not writable by current thread.");
      if (locals.Activity != ThreadActivity.None)
        throw new GuardException("Thread is already reading or writing the object.");
      return true;
    }
    [Pure]
    public bool CanStartWritingTransitively{
      get {
        if (this.CanStartWriting)
          return true;
        Commitment commitment = owner as Commitment;
        if (commitment != null)
          return commitment.owner.CanStartWritingTransitively;
        else
          return false;
      }
    }

    #region Unpack/Pack methods
    /// <summary>
    /// Starts writing the resource; starts writing any transitive owners as necessary.
    /// </summary>
    /// <returns>The furthest transitive owner that was not yet writing.</returns>
    /// 
    [return:Microsoft.Contracts.NotNull]
    public Guard/*!*/ StartWritingTransitively(){
      Guard rootFrame;
      Commitment commitment = owner as Commitment;
      if (commitment != null)
        rootFrame = commitment.owner.StartWritingTransitively();
      else
        rootFrame = this;
      StartWriting();
      return rootFrame;
    }
    /// <summary>
    /// Ends writing the resource; ends writing any transitive reps as necessary.
    /// </summary>
    public void EndWritingTransitively() {
      EndWriting(true, false);
    }

    /// <summary>
    /// Starts writing the resource.
    /// </summary>
    public void StartWriting() {
      //      Console.WriteLine("StartWriting: " + locals.ToString());
      CheckCanStartWriting();
      RegisterSharedFrames();
      Locals.Activity = ThreadActivity.Writing;
      foreach (RepFrame repFrame in repFrames.Values)
        repFrame.Release();
      repFrames.Clear();
      sharedFrames.Clear();
    }
    void EndWriting(bool transitively, bool reflexively) {
      LocalData locals = Locals;
      if (locals.Activity != ThreadActivity.Writing)
        if (reflexively)
          return;
        else
          throw new GuardException("Thread is not writing object.");
      repFrames.Clear();
      sharedFrames.Clear();
      initFrameSets();
      if (transitively)
        foreach (RepFrame repFrame in repFrames.Values)
          repFrame.frame.EndWriting(true, true);
      checkInvariant(true);
      foreach (RepFrame repFrame in repFrames.Values)
        repFrame.Commit(this);
      locals.Activity = ThreadActivity.None;
    }

    public static void StartWritingFrame([NotNull] object o, [NotNull] Type t) { }
    public static void EndWritingFrame([NotNull] object o, [NotNull] Type t) { }

    // The next two pairs of methods are for use when an object is being exposed at
    // one particular type, *without* being unpacked at all subtypes (which is how
    // the "normal" unpacking is done).

    // The first pair, WritingAtNop, is for those occurrences where nothing
    // should be done at runtime, but downstream tools may still need to know
    // that the object is being unpacked.
    public static void StartWritingAtNop([NotNull] object o, [NotNull] Type t) { }
    public static void EndWritingAtNop([NotNull] object o, [NotNull] Type t) { }

    // The second pair, WritingAtTransitively, behaves at runtime just as WritingTransitively,
    // but it knows to not check the invariant for any subtype below t.
    [return: Microsoft.Contracts.NotNull]
    public Guard/*!*/ StartWritingAtTransitively([NotNull] Type t) { return this.StartWritingTransitively(); }
    public void EndWritingAtTransitively([NotNull] Type t) { this.EndWriting(true, false); }
    #endregion Unpack/Pack methods

    /// <summary>
    /// Commits the resource.
    /// </summary>
    /// <param name="owner">The new owner.</param>
    /// <returns>A new commitment.</returns>
    /// <remarks>
    /// A thread that calls this method afterwards no longer has access to the object.
    /// Any thread can gain access to the object by calling the <see cref="Commitment.Release"/> method on the new commitment.
    /// </remarks>
    Commitment Commit(Guard/*!*/ owner) {
      LocalData locals = Locals;
      if (locals.Capability != ThreadCapability.Writable)
        throw new GuardException("Object is not writable by current thread.");
      if (locals.SharingMode != SharingMode.Unshared)
        throw new GuardException("Object is shared.");
      if (locals.Activity != ThreadActivity.None)
        throw new GuardException("Thread is still reading or writing object.");
      Commitment commitment = new Commitment(this, owner);
      this.owner = commitment;
      locals.Capability = ThreadCapability.None;
      return commitment;
    }

    /// <summary>
    /// Adds a resource to this guard's set of <i>reps</i>.
    /// </summary>
    /// <param name="rep">The resource being added.</param>
    /// <remarks>
    /// When a guard ends writing, it gains ownership of its reps.
    /// </remarks>
    public void AddRep(Guard/*!*/ rep) {
      LocalData locals = Locals;
      if (locals.Activity != ThreadActivity.Writing)
        throw new GuardException("Thread is not writing the object.");
      repFrames[rep] = new RepFrame(rep);
    }

    /// <summary>
    /// Adds an object to this guard's set of <i>reps</i>.
    /// </summary>
    /// <param name="repObject">The object being added.</param>
    /// <remarks>
    /// If <paramref name="repObject"/> is not a guarded object, the method does nothing.
    /// </remarks>
    public void AddRepObject(object repObject){
      if (repObject == null) return;
      Guard g = Guard.GetObjectGuard(repObject);
      if (g != null)
        AddRep(g);
    }

    /// <summary>
    /// Adds a frame to this guard's set of <i>reps</i>.
    /// </summary>
    /// <remarks>
    /// If <paramref name="repObject"/> is not a guarded object, the method does nothing.
    /// </remarks>
    public void AddRepFrame(object o, Type t){
      Guard g = Guard.GetFrameGuard(o, t);
      if (g != null)
        AddRep(g);
    }

    /// <summary>
    /// Turns this unshared resource into a lock-protected resource.
    /// </summary>
    /// <remarks>
    /// When this method returns, only the current thread shares the resource.
    /// Share the resource with other threads using
    /// the <see cref="AddLockProtectedCertificate"/> method
    /// or
    /// the <see cref="CreateThreadStartForLockProtected"/> method.
    /// </remarks>
    public void ShareLockProtected(){
      Share(SharingMode.LockProtected);
    }

    /// <summary>
    /// Turns the unshared resource into an immutable resource.
    /// </summary>
    /// <remarks>
    /// When this method returns, only the current thread shares the resource.
    /// Share the resource with other threads using
    /// the <see cref="AddImmutableCertificate"/> method
    /// or the <see cref="CreateThreadStartForImmutable"/> method.
    /// </remarks>
    public void ShareImmutable(){
      Share(SharingMode.Immutable);
    }

    void Share(SharingMode mode){
      LocalData locals = Locals;
//      Console.WriteLine("Share: " + locals.ToString() + ", asked to share as: " + mode.ToString());
      if (mode != SharingMode.Unshared && locals.SharingMode == mode)
        return;
      if (locals.Capability != ThreadCapability.Writable)
        throw new GuardException("Object is not writable by the current thread.");
      if (locals.Activity != ThreadActivity.None)
        throw new GuardException("Thread is still reading or writing the object.");
      if (locals.SharingMode != SharingMode.Unshared)
        throw new GuardException("Object is already shared.");
      locals.SharingMode = mode;
      switch (mode){
        case SharingMode.LockProtected:
          locals.Capability = ThreadCapability.None;
          scheduler = new Scheduler();
          break;
        case SharingMode.Unshared:
          locals.Capability = ThreadCapability.None;
          break;
        default:
          // assert mode == SharingMode.Immutable;
          locals.Capability = ThreadCapability.Readable;
          break;
      }
//      Console.WriteLine("Share: local state now: " + locals.ToString());
    }

    /// <summary>
    /// Acquires exclusive access to this resource.
    /// </summary>
    /// <param name="condition">If not null, indicates when the thread can acquire the resource.</param>
    public void AcquireForWriting(ThreadConditionDelegate condition){
      LocalData locals = Locals;
      if (locals.SharingMode != SharingMode.LockProtected)
        throw new GuardException("Object is not lock-protected.");
      if (locals.Capability != ThreadCapability.None)
        throw new GuardException("Thread has already acquired the object.");
      locals.Capability = ThreadCapability.Readable; // Allow condition code to read the object.
      scheduler.AcquireForWriting(condition);
      locals.Capability = ThreadCapability.Writable;
    }

    /// <summary>
    /// Relinquishes exclusive access to this resource.
    /// </summary>
    public void ReleaseForWriting(){
      LocalData locals = Locals;
      if (locals.SharingMode != SharingMode.LockProtected)
        throw new GuardException("Object is not lock-protected.");
      if (locals.Capability != ThreadCapability.Writable)
        throw new GuardException("Thread has not acquired the object for writing.");
      if (locals.Activity != ThreadActivity.None)
        throw new GuardException("Thread is still reading or writing the object.");
      locals.Capability = ThreadCapability.Readable; // Allow condition code to read the object.
      scheduler.ReleaseForWriting();
      locals.Capability = ThreadCapability.None;
    }

    /// <summary>
    /// Acquires read access to this resource.
    /// </summary>
    /// <param name="condition">If not null, indicates when the thread can acquire the resource.</param>
    public void AcquireForReading(ThreadConditionDelegate condition){
      LocalData locals = Locals;
      if (locals.SharingMode != SharingMode.LockProtected)
        throw new GuardException("Object is not lock-protected.");
      if (locals.Capability != ThreadCapability.None)
        throw new GuardException("Thread has already acquired the object.");
      locals.Capability = ThreadCapability.Readable; // Allow condition code to read the object.
      scheduler.AcquireForReading(condition);
    }

    /// <summary>
    /// Relinquishes read access to this resource.
    /// </summary>
    public void ReleaseForReading(){
      LocalData locals = Locals;
      if (locals.SharingMode != SharingMode.LockProtected)
        throw new GuardException("Object is not lock-protected.");
      if (locals.Capability != ThreadCapability.Readable)
        throw new GuardException("Thread has not acquired the object for reading.");
      if (locals.Activity != ThreadActivity.None)
        throw new GuardException("Thread is still reading the object.");
      scheduler.ReleaseForReading();
      locals.Capability = ThreadCapability.None;
    }

    /// <summary>
    /// Adds a resource to this guard's set of <i>lock-protected certificates</i>.
    /// </summary>
    /// <param name="guard">The resource being added.</param>
    /// <remarks>
    /// When a thread subsequently starts reading or writing this guard,
    /// the resource is shared with the thread.
    /// </remarks>
    public void AddLockProtectedCertificate(Guard/*!*/ guard) {
      AddSharedFrame(guard, SharingMode.LockProtected);
    }

    /// <summary>
    /// Adds a resource to this guard's set of <i>immutable certificates</i>.
    /// </summary>
    /// <param name="guard">The resource being added.</param>
    /// <remarks>
    /// When a thread subsequently starts reading or writing this guard,
    /// the resource is shared with the thread.
    /// </remarks>
    public void AddImmutableCertificate(Guard/*!*/ guard) {
      AddSharedFrame(guard, SharingMode.Immutable);
    }

    void AddSharedFrame(Guard/*!*/ frame, SharingMode mode) {
      frame.Share(mode);
      LocalData locals = Locals;
      if (locals.Activity != ThreadActivity.Writing)
        throw new GuardException("Thread is not writing the object.");
      sharedFrames[frame] = mode;
    }

    /// <summary>
    /// Stores a certificate for a lock-protected object.
    /// Does nothing if the object is not guarded.
    /// </summary>
    /// <param name="sharedObject">The object for which a certificate is stored.</param>
    /// <seealso cref="AddLockProtectedCertificate"/>
    public void AddObjectLockProtectedCertificate(object sharedObject){
      if (sharedObject == null) return;
      Guard g = Guard.GetObjectGuard(sharedObject);
      if (g != null)
        AddLockProtectedCertificate(g);
    }

    /// <summary>
    /// Stores a certificate for an immutable object.
    /// Does nothing if the object is not guarded.
    /// </summary>
    /// <param name="sharedObject">The object for which a certificate is stored.</param>
    /// <seealso cref="AddLockProtectedCertificate"/>
    public void AddObjectImmutableCertificate(object sharedObject){
      if (sharedObject == null) return;
      Guard g = Guard.GetObjectGuard(sharedObject);
      if (g != null)
        AddImmutableCertificate(g);
    }

    void RegisterSharingMode(SharingMode mode){
      LocalData sharedFrameLocals = Locals;
      sharedFrameLocals.SharingMode = mode;
      if (mode == SharingMode.Immutable)
        sharedFrameLocals.Capability = ThreadCapability.Readable;
      else if (mode == SharingMode.Unshared)
        sharedFrameLocals.Capability = ThreadCapability.Writable;
    }

    void RegisterSharedFrames(){
      foreach (DictionaryEntry entry in sharedFrames){
        Guard sharedFrame = (Guard)entry.Key;
        //^ assume sharedFrame != null;
        object value = entry.Value;
        if (value == null) continue;
        SharingMode mode = (SharingMode)value;
        sharedFrame.RegisterSharingMode(mode);
      }
    }

    class ThreadStartTarget{
      Guard frame;
      GuardThreadStart threadStart;
      SharingMode sharingMode;

      public ThreadStartTarget(Guard frame, GuardThreadStart threadStart, SharingMode sharingMode){
        this.frame = frame;
        this.threadStart = threadStart;
        this.sharingMode = sharingMode;
      }

      public void Start(){
        if (this.frame == null){
          // this makes Start() non-re-entrant
          throw new GuardException("Start() method can be called at most once.");
        }
        frame.RegisterSharingMode(sharingMode);
        this.frame = null;
        threadStart();
      }
    }

    ThreadStart CreateThreadStart(GuardThreadStart threadStart, SharingMode sharingMode){
      Share(sharingMode);
      return new ThreadStart(new ThreadStartTarget(this, threadStart, sharingMode).Start);
    }
  
    /// <summary>
    /// Use this method to share the resource with a new thread.
    /// </summary>
    /// <param name="threadStart">A method to be executed by the new sharing thread.</param>
    /// <returns>A delegate that shares the resource with the thread calling it (which is typically a newly started thread)
    /// and then calls <paramref name="threadStart"/>.</returns>
    public ThreadStart CreateThreadStartForImmutable(GuardThreadStart threadStart){
      return CreateThreadStart(threadStart, SharingMode.Immutable);
    }

    /// <summary>
    /// Use this method to share the resource with a new thread.
    /// </summary>
    /// <param name="threadStart">A method to be executed by the new sharing thread.</param>
    /// <returns>A delegate that shares the resource with the thread calling it (which is typically a newly started thread)
    /// and then calls <paramref name="threadStart"/>.</returns>
    public ThreadStart CreateThreadStartForLockProtected(GuardThreadStart threadStart){
      return CreateThreadStart(threadStart, SharingMode.LockProtected);
    }
    /// <summary>
    /// Use this method to transfer the resource to a new thread.
    /// </summary>
    /// <param name="threadStart">A method to be executed by the new standalone thread.</param>
    /// <returns>A delegate that transfers the resource to the thread calling it (which is typically a newly started thread)
    /// and then calls <paramref name="threadStart"/>.</returns>
    public ThreadStart CreateThreadStartForOwn(GuardThreadStart threadStart){
//      Console.WriteLine("CreateThreadStartForOwn: " + threadStart.ToString());
      return CreateThreadStart(threadStart, SharingMode.Unshared);
    }

    /// <summary>
    /// Holds the frame guard getter delegates of the guarded classes loaded into the AppDomain.
    /// </summary>
    /// <remarks>
    /// Lock this object to access it.
    /// </remarks>
    static readonly Hashtable/*<Type,FrameGuardGetter!>!*/ frameGuardGetters = new Hashtable();

    public static void RegisterGuardedClass(Type t, FrameGuardGetter getter) {
      if (getter == null)
        throw new ArgumentNullException("getter");
#if !SINGULARITY
      if (System.Reflection.Assembly.GetCallingAssembly() != t.Assembly)
        throw new ArgumentException("An assembly can register only its own types.");
#endif
      lock (frameGuardGetters) {
        frameGuardGetters.Add(t, getter);
      }
    }

    /// <summary>
    /// Returns the frame guard of object <paramref name="o"/> at type <paramref name="t"/>,
    /// or <code>null</code> if <paramref name="t"/> is not a guarded class.
    /// </summary>
    public static Guard GetFrameGuard([NotNull] object o, [NotNull] Type t){
      FrameGuardGetter getter;
      // The Hashtable documentation allows one writer and multiple readers to access a non-synchronized Hashtable concurrently.
      // See the documentation for the System.Collections.Hashtable.Synchronized method.
      getter = (FrameGuardGetter)frameGuardGetters[t];
      return getter == null ? null : getter(o);
    }

    /// <summary>
    /// Returns the guard of object <paramref name="o"/>, or
    /// <code>null</code> if <paramref name="o"/> is not guarded.
    /// </summary>
    public static Guard GetObjectGuard([NotNull] object o){
      Type t = o.GetType();
      while (t != null){
        Guard guard = GetFrameGuard(o, t);
        if (guard != null)
          return guard;
        t = t.BaseType;
      }
      return null;
    }

    [Pure]
    public static bool IsConsistent([NotNull] object o){
      Guard objectGuard = GetObjectGuard(o);
      if (objectGuard != null){
        return objectGuard.CanStartWriting;
      }else{
        return true; // Objects that do not have an invariant are always consistent.
      }
    }

    [Pure]
    public static bool IsPeerConsistent([NotNull] object o){
      return IsConsistent(o);
    }

    [Pure]
    public bool IsExposable{
      get{
        return this.CanStartWritingTransitively;
      }
    }

    [Pure]
    public static bool FrameIsExposable([NotNull] object o, [NotNull] Type t){
      Guard guard = GetFrameGuard(o, t);
      return guard == null ? true : guard.IsExposable;
    }

    [Pure]
    public static bool BaseIsConsistent([NotNull] object o, [NotNull] Type t){
      // System.Reflection does not seem to allow one to express a base call; this is a workaround.
      return FrameIsExposable(o, t.BaseType);
    }

    [Pure]
    public bool IsExposed{
      get{
        return this.Activity == ThreadActivity.Writing;
      }
    }

    [Pure]
    public static bool FrameIsExposed([NotNull] object o, [NotNull] Type t){
      Guard guard = GetFrameGuard(o, t);
      return guard == null ? true : guard.IsExposed;
    }

    [Pure]
    public bool IsPrevalid{
      get{
        LocalData locals = Locals;
        if (locals.Activity != ThreadActivity.Writing)
          return false;
        repFrames.Clear();
        sharedFrames.Clear();
        initFrameSets();
        foreach (RepFrame repFrame in repFrames.Values)
          if (!repFrame.frame.IsExposable)
            return false;
        return true;
      }
    }

    [Pure]
    public static bool FrameIsPrevalid([NotNull] object o, [NotNull] Type t){
      Guard guard = GetFrameGuard(o, t);
      return guard == null ? true : guard.IsPrevalid;
    }

    [Pure]
    public bool IsValid{
      get{
        return this.IsPrevalid && this.checkInvariant(false);
      }
    }

    [Pure]
    public static bool FrameIsValid([NotNull] object o, [NotNull] Type t){
      Guard guard = GetFrameGuard(o, t);
      return guard == null ? true : guard.IsValid;
    }

    public static void ShareLockProtected([NotNull] object o){
      Guard guard = GetObjectGuard(o);
      if (guard != null)
        guard.ShareLockProtected();
    }

    [Pure]
    public static bool IsLockProtected(object o){
      Guard g = GetObjectGuard(o);
      return g != null ? g.SharingMode == SharingMode.LockProtected : true;
    }

    [Confined]
    public static void ModifiesObject(object o){}
    [Confined]
    public static void ModifiesArray(object o) { }
    [Pure]
    public static void ModifiesPeers(object o) { }
    [Pure]
    public static void ModifiesNothing(object o) { }

    /// <summary>
    /// In a method's ensures clause, indicates that <paramref name="o"/> was not allocated in the pre-state.
    /// Note: this is a temporary measure that will be replaced with a more modular construct in the future.
    /// </summary>
    [Confined]
    public static bool IsNew(object o) { return true; }

    /// <summary>
    /// Used in the Boogie bytecode translator.
    /// </summary>
    public static void NoOp(){}
  }
}

namespace Microsoft.Contracts{
#if CCINamespace
  using Microsoft.Cci;
#endif
  /// <summary>
  /// Indicates that the field refers to a lock-protected object.
  /// </summary>
  /// <remarks>
  /// This attribute causes the Spec# compiler to emit a call to the <see cref="Microsoft.Contracts.Guard.AddObjectLockProtectedCertificate"/>
  /// method in its <see cref="Microsoft.Contracts.InitGuardSetsDelegate"/> implementation.
  /// </remarks>
  [AttributeUsage(AttributeTargets.Field|AttributeTargets.Parameter)]
  public class LockProtectedAttribute : Attribute {}
  /// <summary>
  /// Indicates that the method requires that the target is lock-protected.
  /// </summary>
  /// <remarks>
  /// This attribute causes the Spec# compiler's ThreadStart conversion feature
  /// to share the lock-protected target object
  /// with the newly started thread.
  /// </remarks>
  [AttributeUsage(AttributeTargets.Method)]
  public class RequiresLockProtectedAttribute : Attribute {}
  /// <summary>
  /// Indicates that the field refers to an immutable object.
  /// </summary>
  /// <remarks>
  /// This attribute causes the Spec# compiler to emit a call to the <see cref="Microsoft.Contracts.Guard.AddObjectImmutableCertificate"/>
  /// method in its <see cref="Microsoft.Contracts.InitGuardSetsDelegate"/> implementation.
  /// </remarks>
  [AttributeUsage(AttributeTargets.Interface | AttributeTargets.Class | AttributeTargets.Field, AllowMultiple = false, Inherited = true)]
  public sealed class ImmutableAttribute : Attribute { }
  /// <summary>
  /// Indicates that the method requires that the target is writeable.
  /// </summary>
  /// <remarks>
  /// This attribute causes the Spec# compiler's ThreadStart conversion feature to transfer the target object
  /// to the newly started thread.
  /// </remarks>
  [AttributeUsage(AttributeTargets.Method)]
  public class RequiresCanWriteAttribute : Attribute {}
  /// <summary>
  /// Indicates that the method requires that the target is immutable.
  /// </summary>
  /// <remarks>
  /// This attribute causes the Spec# compiler's ThreadStart conversion feature to share the immutable target object
  /// with the newly started thread.
  /// </remarks>
  [AttributeUsage(AttributeTargets.Method)]
  public class RequiresImmutableAttribute : Attribute {}
  /// <summary>
  /// Indicates that the method reads the target.
  /// </summary>
  /// <remarks>
  /// This attribute causes the Spec# compiler to enclose the method's body in a <c>read (this)</c> statement.
  /// </remarks>
  [AttributeUsage(AttributeTargets.Method)]
  public class ReaderAttribute : Attribute {}
  /// <summary>
  /// Indicates that the method writes the target.
  /// </summary>
  /// <remarks>
  /// This attribute causes the Spec# compiler to enclose the method's body in a <c>write (this)</c> statement.
  /// </remarks>
  [AttributeUsage(AttributeTargets.Method)]
  public class WriterAttribute : Attribute {}
  [AttributeUsage(SpecTargets.Code,AllowMultiple=false, Inherited = true)]
  public sealed class ConfinedAttribute: AttributeWithContext{
  }
  [Obsolete("Use Microsoft.Contracts.NoDefaultContract instead")]
  [AttributeUsage(AttributeTargets.Method | AttributeTargets.Property | AttributeTargets.Class | AttributeTargets.Constructor, AllowMultiple = true, Inherited = false)]
  public sealed class NoDefaultActivityAttribute: AttributeWithContext{
  }
  [AttributeUsage(AttributeTargets.Method | AttributeTargets.Property | AttributeTargets.Class | AttributeTargets.Constructor | AttributeTargets.Parameter,AllowMultiple=true, Inherited = false)]
  public sealed class NoDefaultContractAttribute: AttributeWithContext{
  }
  [Obsolete("Use Microsoft.Contracts.Rep or Microsoft.Contracts.Peer instead")]
  [AttributeUsage(AttributeTargets.Field | AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
  public sealed class OwnedAttribute: Attribute{
    /// <summary>
    /// True if the field is owned; false otherwise.
    /// </summary>
    public bool Value;
    /// <summary>
    /// True if the field is a peer field; false otherwise.
    /// </summary>
    public bool Peer;
    public OwnedAttribute() { this.Value = true; this.Peer = false; }
    public OwnedAttribute(bool value) { this.Value = value; this.Peer = false; }
    public OwnedAttribute(string value) {
      switch (value) {
        case "peer":
          this.Value = false;
          this.Peer = true;
          break;
        case "this":
          this.Value = true;
          this.Peer = false;
          break;
        default:
          System.Diagnostics.Debug.Assert(false);
          break;
      }
    }
  }
  [AttributeUsage(AttributeTargets.Field | AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
  public sealed class RepAttribute : Attribute {
  }
  [AttributeUsage(AttributeTargets.Field | AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
  public sealed class PeerAttribute : Attribute {
  }
  /// <summary>
  /// Fields of array-type or subtype of IEnumerable can be marked ElementsRep meaning that the elements of the 
  /// array or collection are rep of the array or collection. 
  /// </summary>
  [AttributeUsage(AttributeTargets.Field, AllowMultiple = false, Inherited = false)]
  public sealed class ElementsRepAttribute : AttributeWithContext {
  }
  /// <summary>
  /// Fields of array-type or subtype of IEnumerable can be marked ElementsPeer meaning that the elements of the 
  /// array or collection are peer of the array or collection. 
  /// </summary>
  [AttributeUsage(AttributeTargets.Field, AllowMultiple = false, Inherited = false)]
  public sealed class ElementsPeerAttribute : AttributeWithContext {
  }
  /// <summary>
  /// Methods of subtypes of IEnumerable can be marked Element meaning that the method returns an 
  /// element of the collection. 
  /// </summary>
  [AttributeUsage(AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
  public sealed class ElementAttribute : AttributeWithContext {
  }
  /// <summary>
  /// Methods of subtypes of IEnumerable can be marked ElementCollection meaning that the method returns 
  /// a set of elements of the collection. 
  /// </summary>
  [AttributeUsage(AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
  public sealed class ElementCollectionAttribute : AttributeWithContext {
  }
  /// <summary>
  /// Used to ensure acyclicity of method call chains in specifications of methods.
  /// Indicates the maximum number of method calls before the call chain terminates.
  /// E.g. zero if method's specification does not contain method calls.
  /// </summary>
  [AttributeUsage(AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
  public sealed class RecursionTerminationAttribute : AttributeWithContext {
    public int level;
    public RecursionTerminationAttribute() { this.level = 0; }
    public RecursionTerminationAttribute(int level) { this.level = level; }
  }
  [AttributeUsage(AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
  public sealed class NoReferenceComparisonAttribute : AttributeWithContext {
  }
  [AttributeUsage(AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
  public sealed class ResultNotNewlyAllocatedAttribute : AttributeWithContext {
  }
  /// <summary>
  /// Indicates that a parameter, or the receiver parameter if applied to a method or constructor, starts in an unowned state and may cause the owner to change.
  /// </summary>
  [AttributeUsage(AttributeTargets.Parameter | AttributeTargets.Method | AttributeTargets.Constructor, AllowMultiple=false)]
  public sealed class CapturedAttribute : Attribute{
  }
  [AttributeUsage(AttributeTargets.Field, AllowMultiple = true, Inherited = false)]
  public sealed class DependentAttribute : Attribute {
    /// <summary>
    /// The type that is allowed to have an invariant referring to the field
    /// this attribute is attached to.
    /// </summary>
    public Type otherType;
    public DependentAttribute(Type otherType) { this.otherType = otherType; }
  }
  public sealed class Owner{
    /// <summary>
    /// As seen by the static program verifier:  returns true iff c and d are owned by the same owner or
    /// if they have no owner and belong to the same peer group.
    /// Dynamically, this method always returns true.  If you want the negation, you Different.
    /// </summary>
    /// <param name="c"></param>
    /// <param name="d"></param>
    /// <returns></returns>
    [Pure]
    public static bool Same([NotNull] [Delayed] object c, [NotNull] object d) { return true; }
    /// <summary>
    /// As seen by the static program verifier:  returns false iff c and d are owned by the same owner or
    /// if they have no owner and belong to the same peer group.
    /// Dynamically, this method always returns true.  If you want the negation, you Same.
    /// </summary>
    /// <param name="c"></param>
    /// <param name="d"></param>
    /// <returns></returns>
    [Pure]
    public static bool Different([NotNull] [Delayed] object c, [NotNull] object d) { return true; }
    /// <summary>
    /// As seen by the static program verifier:  returns true iff subject has no owner.
    /// Dynamically, this method always returns true.
    /// </summary>
    /// <param name="c"></param>
    /// <returns></returns>
    [Pure]
    public static bool None([NotNull] [Delayed] object c) { return true; }
    /// <summary>
    /// As seen by the static program verifier:  returns true iff subject is owned by (owner,frame).
    /// Dynamically, this method always returns true.
    /// </summary>
    /// <param name="subject"></param>
    /// <param name="owner"></param>
    /// <param name="frame"></param>
    /// <returns></returns>
    [Pure]
    public static bool Is([NotNull] [Delayed] object subject, [NotNull] object owner, [NotNull] Type frame) { return true; }
    /// <summary>
    /// As seen by the static program verifier:  returns true iff subject has no owner and is in
    /// in peer group represented by itself.  That is, returns true iff the subject's owner is
    /// the same as it is in the post-state of a non-capturing constructor.
    /// Dynamically, this method always returns true.
    /// </summary>
    /// <param name="c"></param>
    /// <returns></returns>
    [Pure]
    public static bool New([NotNull] [Delayed] object c) { return true; }
    /// <summary>
    /// As seen by the static program verifier:  Requires that subject initially has no owner, and sets the owner of
    /// subject and any other objects in its peer group to (owner,frame).
    /// That is:
    ///   requires Owner.None(subject);
    ///   ensures Owner.Is(subject, owner, frame);
    /// Dynamically, this method is a no-op.
    /// </summary>
    /// <param name="subject"></param>
    /// <param name="owner"></param>
    /// <param name="frame"></param>
    public static void Assign([NotNull] [Delayed] object subject, [NotNull] object owner, [NotNull] Type frame) { }
    /// <summary>
    /// As seen by the static program verifier:  Requires that "subject" initially has no owner, and sets the owner of
    /// "subject" and any other objects in its peer group to the same owner or peer group as "peer"..
    /// That is:
    ///   requires Owner.None(subject);
    ///   ensures Owner.Same(subject, peer);
    /// Dynamically, this method is a no-op.
    /// </summary>
    /// <param name="subject"></param>
    /// <param name="peer"></param>
    public static void AssignSame([NotNull] [Delayed] object subject, [NotNull] object peer) { }
  }
  public class ObjectInvariantException : Microsoft.Contracts.GuardException{
    public ObjectInvariantException() : base("Object invariant does not hold.") {}
  }
  ///<summary>
  ///Instructs downstream tools to assume the correctness of this assembly, type or member without performing any verification.
  /// Can use [SkipVerification(false)] to explicitly mark assembly, type or member as one to have verification performed on it.
  /// Most specific element found (member, type, then assembly) takes precedence.
  /// (That is useful if downstream tools allow a user to decide which polarity is the default, unmarked case.)
  ///</summary>
  ///<remarks>
  ///Apply this attribute to a type to apply to all members of the type, including nested types.
  ///Apply this attribute to an assembly to skip verification of all types and members of the assembly.
  /// Default is true, so [SkipVerification] is the same as [SkipVerification(true)].
  ///</remarks>
  [Obsolete("Use Microsoft.Contracts.Verify instead")]
  [AttributeUsage(AttributeTargets.Assembly | AttributeTargets.Class | AttributeTargets.Struct | AttributeTargets.Method | AttributeTargets.Constructor)]
  public sealed class SkipVerificationAttribute : Attribute { 
    public bool Value;
    public SkipVerificationAttribute() { this.Value = true; }
    public SkipVerificationAttribute(bool value) { this.Value = value; }
  }
  ///<summary>
  ///Instructs downstream tools whether to assume the correctness of this assembly, type or member without performing any verification or not.
  /// Can use [Verify(false)] to explicitly mark assembly, type or member as one to *not* have verification performed on it.
  /// Most specific element found (member, type, then assembly) takes precedence.
  /// (That is useful if downstream tools allow a user to decide which polarity is the default, unmarked case.)
  ///</summary>
  ///<remarks>
  ///Apply this attribute to a type to apply to all members of the type, including nested types.
  ///Apply this attribute to an assembly to apply to all types and members of the assembly.
  /// Apply this attribute to a property to apply to both the getter and setter.
  ///Default is true, so [Verify] is the same as [Verify(true)].
  ///</remarks>
  [AttributeUsage(AttributeTargets.Assembly | AttributeTargets.Class | AttributeTargets.Struct | AttributeTargets.Method | AttributeTargets.Constructor | AttributeTargets.Property)]
  public sealed class VerifyAttribute : Attribute {
    public bool Value;
    public VerifyAttribute() { this.Value = true; }
    public VerifyAttribute(bool value) { this.Value = value; }
  }

  [AttributeUsage(AttributeTargets.Method | AttributeTargets.Field | AttributeTargets.Parameter | AttributeTargets.ReturnValue)]
  public sealed class AdditiveAttribute : Attribute 
  {
    public bool Value;
    public AdditiveAttribute() { this.Value = true; }
    public AdditiveAttribute(bool value) { this.Value = value; }
  }
  [AttributeUsage(AttributeTargets.Method | AttributeTargets.Parameter | AttributeTargets.ReturnValue)]
  public sealed class InsideAttribute : Attribute {
    public bool Value;
    public InsideAttribute() { this.Value = true; }
    public InsideAttribute(bool value) { this.Value = value; }
  }
}

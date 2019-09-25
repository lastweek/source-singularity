// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace System {
  using Microsoft.Bartok.Runtime;
  using System.Reflection;
  using System.Text;
  using System.Runtime.CompilerServices;
  using System.Runtime.InteropServices;
  using System.Threading;
#if SINGULARITY
  using SystemType = Microsoft.Singularity.V1.Types.SystemType;
#endif

  // BUGBUG: System.VTable.initType code locks on RuntimeType objects.  This is
  // incorrect since RuntimeTypes are user-visible.

  [StructLayout(LayoutKind.Sequential)]
#if SINGULARITY
  [AccessedByRuntime("Referenced from C++")]
#else
  [CCtorIsRunDuringStartup]
  [Serializable]
#endif
  internal sealed partial class RuntimeType : Type {

      // expand as needed, but also see/use TypeAttributes
      // matches convert\ContainerInfo.cs::Enum_Kind
      internal enum Enum_Kind {
          NotSpecial         = 0,
              Vector         = 1,
              RectangleArray = 2,
              Primitive      = 3,
              Enum           = 4,
              OtherValueType = 5
      };

      private int _pData = 0;
      [RequiredByBartok]
      private readonly Module module;
      [RequiredByBartok]
      private readonly RuntimeType enclosingType;
#if SINGULARITY
      [AccessedByRuntime("Referenced from C++")]
#endif
      [RequiredByBartok]
      private readonly String name;
      [RequiredByBartok]
      private readonly String nameSpace;
      [RequiredByBartok]
      internal readonly RuntimeType baseType;
      [RequiredByBartok]
      internal readonly System.RuntimeType[] interfaces;
      [RequiredByBartok]
      internal readonly Enum_Kind kind;
      [RequiredByBartok]
      internal readonly int rank;
      [RequiredByBartok]
      internal readonly TypeAttributes attributes;
#if SINGULARITY
      [AccessedByRuntime("Referenced from C++")]
#endif
      [RequiredByBartok]
      internal readonly VTable classVtable;

      // Putting these here for now because we need them for classes
      // and interfaces, and I don't think we build VTable objects for
      // interfaces:

      [RequiredByBartok]
      internal readonly System.UIntPtr cctor; // HACK: function pointer
      [RequiredByBartok]
      internal readonly System.UIntPtr ctor;  // HACK: function pointer
      [RequiredByBartok]
      internal Exception cctorException;

      [RequiredByBartok]
      internal TypeInitState cctorState;
      [RequiredByBartok]
      internal System.Threading.Thread cctorThread;

#if SINGULARITY
      // This is a cache for the corresponding system-wide type
      private SystemType systemType;
#endif
      
#if DEBUG
      private static bool doneWarning;
#endif

      internal RuntimeType() {
          VTable.NotReached("RuntimeType constructor not supported");
      }

      [NoHeapAllocation]
      public override bool IsSubclassOf(Type c) {
            Type p = this;
            if (p == c)
                return false;
            while (p != null) {
                if (p == c)
                    return true;
                p = p.BaseType;
            }
            return false;
      }

      [Inline]
      [NoBarriers]
      [PreInitRefCounts]
      [NoHeapAllocation]
      public static Type GetTypeFromHandleImpl(RuntimeTypeHandle handle) {
          IntPtr handleAddress = handle.Value;
          return Magic.toType(Magic.fromAddress((UIntPtr) handleAddress));
      }

#if SINGULARITY
      public Module Module {
#else
      public override Module Module {
#endif
          get { return module; }
      }

      public override Assembly Assembly {
          [NoHeapAllocation]
          get { return module.Assembly; }
      }

      public override String Name {
          [NoHeapAllocation]
          get { return name; }
      }

      private void AddFullName(StringBuilder sb) {
          RuntimeType enclosing = this.enclosingType;
          if (enclosing != null) {
              enclosing.AddFullName(sb);
              sb.Append('+');
          }
          else if((nameSpace != null) && (nameSpace != "")) {
              sb.Append(nameSpace);
              sb.Append('.');
          }
          sb.Append(name);
      }          

      public override String FullName {
          get {
              StringBuilder sb = new StringBuilder();
              AddFullName(sb);
              return sb.ToString();
          }
      }

      // Return "<name with namespace", "assembly strong name".
      public override String AssemblyQualifiedName {
          get {
              StringBuilder sb = new StringBuilder();
              AddFullName(sb);
              sb.Append(", ");
              sb.Append(module.Assembly.FullName);
              return sb.ToString();
          }
      }

      /**
       * Returns the base class for a class.  If this is an interface or has
       * no base class null is returned.  Object is the only Type that does not 
       * have a base class.  
       */

      public override Type BaseType {
          [NoHeapAllocation]
          get { return baseType; }
      }

      public override int GetArrayRank() {
          return rank;
      }
 
      public override Type[] GetInterfaces() { 
          Type[] interfaceArray = this.interfaces;
          VTable.Assert(interfaceArray != null);
          int count = interfaceArray.Length;
          if (count == 0) {
              return interfaceArray;
          }
          Type[] interfaceCopy = new Type[count];
          for (int i=0; i<count; i++) {
              interfaceCopy[i] = interfaceArray[i];
          }
          return interfaceCopy;
      }

      [NoHeapAllocation]
      protected override TypeAttributes GetAttributeFlagsImpl() {
          return attributes;
      }

      [NoHeapAllocation]
      protected override bool IsArrayImpl() {
          return this.classVtable.arrayOf != StructuralType.None;
      }

      [NoHeapAllocation]
      protected override bool IsPrimitiveImpl() {
          return kind == Enum_Kind.Primitive;
      }

      [NoHeapAllocation]
      public override Type GetElementType() {
          VTable element = this.classVtable.arrayElementClass;
          return (element != null) ? element.vtableType : null;
      }

      public override String Namespace {
          [NoHeapAllocation]
          get { return nameSpace; }
      }

      internal bool IsVector {
          [NoHeapAllocation]
          get {
              return kind == Enum_Kind.Vector;
          }
      }

      internal bool IsRectangleArray {
          [NoHeapAllocation]
          get {
              return kind == Enum_Kind.RectangleArray;
          }
      }
  }
}

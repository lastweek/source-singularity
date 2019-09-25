//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace System.Runtime.CompilerServices {

  // The InformationCategory and InformationAttribute are used as documentation aids.
  // Place them on an attribute to provide details to the automatically generated
  // attribute documentation.

  internal enum InformationCategory {
      System,
      Runtime,
      CodeLayout,
      Override,
      Research,
      None,
      Ignore
  }

  [AttributeUsage(AttributeTargets.Class, Inherited=false)]
  internal class InformationAttribute : Attribute {
      internal InformationAttribute(string description) 
          : this(InformationCategory.None, description){
      }

      internal InformationAttribute(InformationCategory category) 
          : this(category, null){
      }

      internal InformationAttribute(InformationCategory category, string description) {
          this.category = category;
          this.description = description;
      }
      public InformationCategory Category {
          get { return this.category; }
      }

      public string Description {
          get { return this.description; }
      }

      InformationCategory category;
      string description;
  } 

  // end phx whidbey

  // attribute which causes a warning to be issued if a call to the given
  // method is not devirtualized.
  [Information("Issues a warning if a call to the given method is not devirtualized.")]
  [AttributeUsage(AttributeTargets.Method)]
  [RequiredByBartok]
  internal sealed class AssertDevirtualizeAttribute: Attribute {

  }

  // attribute indicating that the given method is called rarely.  basic
  // blocks that contain calls to rarely-called methods have lower priority
  // in the code layout part of the backend.
  [Information(InformationCategory.CodeLayout,
               "Indicates that the constructor or method is rarely called.  Thus, these " +
               "constructors or methods will not be inlined.  In addition, code layout " +
               "decisions will be made so that the call is moved to the end of a function.")]
  [AttributeUsage(AttributeTargets.Method)]
  [RequiredByBartok]
  internal sealed class CalledRarelyAttribute: Attribute {

  }

  [Information(InformationCategory.CodeLayout,
               "This attribute tells the compiler to inline all occurrences of this constructor " +
               "or method.  Occurrences are not inlined into large functions.  Large is a " +
               "compiler-writer specific notion.  It is not very meaningful to the end programmer " +
               "(150 basic blocks or more than 8000 IR instructions).  This attribute is meant to " +
               "be used only for performance-critical system code, such as the implementation of " +
               "language primitives.   Note that attribute is currently disregarded if the constructor " +
               "or method is marked with the following attributes: RequireStackLink, RequireStackLinkCheck, " +
               "NoStackLinkCheck, NoStackLinkTrans, and NoStackLinkTransCut.")]
  [AttributeUsage(AttributeTargets.Constructor|
                  AttributeTargets.Method)]
  [RequiredByBartok]
#if SINGULARITY
  public sealed class InlineAttribute: Attribute {
#else
  internal sealed class InlineAttribute: Attribute {
#endif

  }

  // stronger Inline attribute.  forces inlining on a method
  // even if the caller is deemed too large for further inlining.
  //
  // This is currently used by GC barrier code.  In general, this attribute
  // should be used with great care.  DO NOT USE IT ELSEWHERE IN THE RUNTIME
  // UNLESS YOU ARE WILLING TO DOCUMENT YOUR USE IN IrSimpleInliner.cs AND
  // Attributes.cs!  AND NEVER USE IT IN APPLICATION OR OS CODE!
  [Information(InformationCategory.CodeLayout,
               "Inline all occurences of this constructor or method, no matter how large the " +
               "function is.  This attribute is disregarded if the constructor or method is marked " +
               "with stack linking operations that cause the Inline attribute to be disregarded.")]
  [AttributeUsage(AttributeTargets.Constructor|
                  AttributeTargets.Method)]
  [RequiredByBartok]
  internal sealed class ForceInlineAttribute: Attribute {

  }

  [Information(InformationCategory.CodeLayout,
               "This attributes tells the compiler never to inline any occurrence of this " +
               "constructor or method.  This attribute is meant to be used for " +
               "performance-critical code, primarily for making sure that the cold code is not inlined.")]
  [AttributeUsage(AttributeTargets.Constructor|
                  AttributeTargets.Method)]
  [RequiredByBartok]
  internal sealed class NoInlineAttribute: Attribute {

  }

  [Information(InformationCategory.CodeLayout,
               "Indicates that all assignments of values of that struct type be done via in-line code.")]
  [AttributeUsage(AttributeTargets.Struct)]
  internal sealed class InlineCopyAttribute: Attribute {
  }

  [Information(InformationCategory.Runtime,
               "Prevents the compiler from inserting array/vector bounds checking.")]
  [AttributeUsage(AttributeTargets.Constructor|
                  AttributeTargets.Method)]
  internal sealed class DisableBoundsChecksAttribute: Attribute {

  }

  [Information(InformationCategory.Runtime,
               "Prevents the compiler from inserting null reference checks.")]
  [AttributeUsage(AttributeTargets.Constructor|
                  AttributeTargets.Method)]
  internal sealed class DisableNullChecksAttribute: Attribute {

  }

  [Information(InformationCategory.CodeLayout,
               "All calls in the method are inlined at least once, unless the method is extremely large.")]
  [AttributeUsage(AttributeTargets.Constructor|
                  AttributeTargets.Method)]
  internal sealed class InlineIntoOnceAttribute: Attribute {
  }

  [Information(InformationCategory.Runtime,
               "The class constructor for the type is run during process start up.  " +
               "You must explicitly add the class")]
  [AttributeUsage(AttributeTargets.Interface|
                  AttributeTargets.Class|
                  AttributeTargets.Struct,
                  Inherited=false)]
  public sealed class CCtorIsRunDuringStartupAttribute : Attribute {
  }

  [Information(InformationCategory.System,
               "Asserts that there is no class constructor for the type.  " +
               "This property is verified by the compiler.")]
  [AttributeUsage(AttributeTargets.Interface|
                  AttributeTargets.Class|
                  AttributeTargets.Struct,
                  Inherited=false)]
  public sealed class NoCCtorAttribute : Attribute {
  }

  [Information(InformationCategory.System,
               "This method will not allocate heap objects, nor will any of the methods " + 
               "it calls.  This property is verified by the compiler.")]
  [AttributeUsage(AttributeTargets.Constructor|
                  AttributeTargets.Method)]
  public sealed partial class NoHeapAllocationAttribute : Attribute {
  }

  // AccessedByRuntimeAttribute must be placed on any type, field, or method
  // that will be accessed by native (non-MSIL) runtime components.  If a field
  // or method is annotated, then the enclosing type must also be annotated.  If
  // a field or method is annotated, then any value types appearing naked (e.g.,
  // S but not S*) in the signature of that member must also be annotated.
  // Items annotated will be emitted to C++ or ASM header files specified by
  // the /GenCppHeader and /GenAsmHeader flags respectively.  These annotations
  // can block optimizations, including but not limited to aggressive field
  // layout and field analysis.
  [Information(InformationCategory.System,
               "The symbol needs to be exported in C++ and assembly headers so that " +
               "runtime native code can use it.")]
  [AttributeUsage(AttributeTargets.Class|
                  AttributeTargets.Struct|
                  AttributeTargets.Interface|
                  AttributeTargets.Method|
                  AttributeTargets.Constructor|
                  AttributeTargets.Field|
                  AttributeTargets.Enum,
                  Inherited=false)]
  [RequiredByBartok]
#if SINGULARITY
  public sealed class AccessedByRuntimeAttribute: Attribute {
#else
  internal sealed class AccessedByRuntimeAttribute: Attribute {
#endif
      public AccessedByRuntimeAttribute(string reason) {
          this.reason = reason;
      }

      public int Option {
          get { return option; }
          set { option = value; }
      }
      public bool AllFields {
          get { return allFields; }
          set { allFields = value; }
      }

      int option;
      string reason;
      bool allFields;
  }

  [Information(InformationCategory.System,
               "This field is defined by native code.")]
  [AttributeUsage(AttributeTargets.Field)]
  public sealed class ExternalStaticDataAttribute : Attribute {
  }

  [Information(InformationCategory.System,
               "Instances of this type will aligned to the specified byte boundary.")]
  [AttributeUsage(AttributeTargets.Struct|
                  AttributeTargets.Class)]
  public sealed class StructAlignAttribute : Attribute {
      public StructAlignAttribute(int align) {}
  }

  [Information(InformationCategory.System,
               "Identifies the largest stack frame used by an extern method.  " +
               "This information is used by the stack linking analysis code to " +
               "assign a frame size to external leaf calls.")]
  [AttributeUsage(AttributeTargets.Method,
                  Inherited=false)]
  public sealed class StackBoundAttribute: Attribute {
      public StackBoundAttribute(int bound) {}
  }

  [Information(InformationCategory.System,
               "Requires the compiler to insert a stack link check for this method.")]
  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Constructor,
                  Inherited=false)]
  public sealed class StackLinkCheckAttribute: Attribute {
  }

  [Information(InformationCategory.System,
               "Requires the compiler to insert")]
  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Constructor,
                  Inherited=false)]
  public sealed class RequireStackLinkAttribute: Attribute {
  }

  [Information(InformationCategory.System,
               "Prevents the compiler from inserting a stack link check for this method.")]
  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Constructor,
                  Inherited=false)]
  public sealed class NoStackLinkCheckAttribute: Attribute {
  }

  [Information(InformationCategory.System,
               "Prevents the compiler from inserting a stack link check for this methods and " +
               "any method in its call tree.  The transitive stack link prevention requirement " +
               "will not cross a method with the NoStackLinkTransCut attribute.  " +
               "It is a compiler error if the transitive requirement fails, or if a cycle exists "+
               "in the call tree (since the stack could grow unbounded without a stack link).")]
  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Constructor,
                  Inherited=false)]
  public sealed class NoStackLinkCheckTransAttribute: Attribute {
  }

  [Information(InformationCategory.System,
               "Stops the transitive stack link checking initiated by the NoStackLinkTrans attribute.  " +
               "This attribute is primarily used to break cycles in call trees.  Use with extreme " +
               "caution since it can break assumptions made by methods with the NoStackLinkTrans " +
               "attribute.")]
  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Constructor,
                  Inherited=false)]
  public sealed class NoStackLinkCheckTransCutAttribute: Attribute {
  }

  [Information("Prevents the compiler from inserting stack overflow checks on function entry.")]
  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Constructor,
                  Inherited=false)]
  [RequiredByBartok]
  public sealed class NoStackOverflowCheckAttribute: Attribute {
  }

  [Information(InformationCategory.Runtime,
               "Identifies a method/field as a compiler intrinsic.  It will be " +
               "generated at compile time.")]
  [AttributeUsage(AttributeTargets.Field|
                  AttributeTargets.Method|
                  AttributeTargets.Constructor,
                  Inherited=false)]
  public sealed class IntrinsicAttribute: Attribute {
      // Intrinsics should never have bodies.  However, csc complains if we
      // mark a property on a struct extern, so we have to give those bodies.
      // Hence this flag.  IgnoreBody=true means discard the body.
      // IgnoreBody=false means it is an error to supply a body.
      public bool IgnoreBody {
          get { return ignoreBody; }
          set { ignoreBody = value; }
      }
      bool ignoreBody;
  }

  [Information(InformationCategory.System,
               "An array of the given field's type should be 'inlined' into " +
               "into the instance rather than having an array reference.")]
  [AttributeUsage(AttributeTargets.Field)]
  [RequiredByBartok]
  internal sealed class InlineVectorAttribute : Attribute {
      public InlineVectorAttribute(int numElements) {}
  }

  // This attribute is used to mark method that needs pushStackMark
  // and popStackMark around calls to it.
  [Information(InformationCategory.System,
               "see [[GC Attributes on Singularity Kernel Calls]]")]
  [AttributeUsage(AttributeTargets.Method,
                  Inherited=false)]
  public sealed class OutsideGCDomainAttribute: Attribute {
  }

  // This attribute is used to mark method that needs enterGCSafteState
  // and leaveGCSafeState around its definition
  [Information(InformationCategory.System,
               "see [[GC Attributes on Singularity Kernel Calls]]")]
  [AttributeUsage(AttributeTargets.Method,
                  Inherited=false)]
  [RequiredByBartok]
  public sealed class ExternalEntryPointAttribute: Attribute {
      public int Option {
          get { return option; }
          set { option = value; }
      }
      public int IgnoreCallerTransition {
          get { return ignoreCallerTransition; }
          set { ignoreCallerTransition = value; }
      }
      int option, ignoreCallerTransition;
  }

  // This attribute is used to mark type/field/methods that are required
  // by Bartok compiler.
  [Information(InformationCategory.Runtime,
               "Used to mark types/fields/methods that are required by the " +
               "Bartok compiler")]
  [AttributeUsage(AttributeTargets.Class |
                  AttributeTargets.Struct |
                  AttributeTargets.Enum |
                  AttributeTargets.Interface |
                  AttributeTargets.Delegate |
                  AttributeTargets.Method |
                  AttributeTargets.Property|
                  AttributeTargets.Constructor |
                  AttributeTargets.Field,
                  Inherited=false)]
  public sealed class RequiredByBartokAttribute: Attribute {
      public RequiredByBartokAttribute() {}
      public RequiredByBartokAttribute(string reason) {
          this.reason = reason;
      }
      string reason;
  }

  /// <summary>
  /// This attribute must be placed on override types that override the class
  /// constructor.  It is a compile-time error if the attribute is missing
  /// during an override.  It is also a compile-time error if it exists and
  /// either the original or the override type does not have a class
  /// constructor.
  /// </summary>
  [Information(InformationCategory.Override,
               "Must be placed on override types that override the class constructor.")]
  [AttributeUsage(AttributeTargets.Class|
                  AttributeTargets.Struct|
                  AttributeTargets.Interface)]
  internal sealed class OverrideCctorAttribute : Attribute {
  }

  /// <summary>
  /// This attribute must be placed on override types that mean to override the
  /// base class.  If a base class is overridden, then either this attribute or
  /// IgnoreOverrideExtendsAttribute must be present.  It is also a compile-time
  /// error if this attribute exists and the override base class is the same as
  /// the original base class.
  /// </summary>
  [Information(InformationCategory.Override,
               "Indicates that an override type is replacing the base class.  " +
               "An override type that overrides the base class must have either " +
               "OverrideExtendsAttribute or IgnoreOverrideExtendsAttribute.")]
  [AttributeUsage(AttributeTargets.Class)]
  internal sealed class OverrideExtendsAttribute : Attribute {
  }

  /// <summary>
  /// This attribute must be placed on override types that override the base
  /// class in the override assembly but do not mean to override the base class
  /// in the actual type.  If a base class is overridden, then either this
  /// attribute or OverrideExtendsAttribute must be present.  It is also a
  /// compile-time error if this attribute exists and the override base class is
  /// the same as the original base class.
  /// </summary>
  [Information(InformationCategory.Override,
               "Indicates that an override type is overriding the base class in" +
               "the override assembly, but not in the actual type.  " +
               "An override type that overrides the base class must have either " +
               "OverrideExtendsAttribute or IgnoreOverrideExtendsAttribute.")]
  [AttributeUsage(AttributeTargets.Class)]
  public sealed class IgnoreOverrideExtendsAttribute : Attribute {
  }

  /// <summary>
  /// This attribute is placed on override types to delete the built-in class
  /// constructor.  Using this is better than overriding with an empty method.
  /// </summary>
  [Information(InformationCategory.Override,
               "Delete the built-in class constructor.")]
  [AttributeUsage(AttributeTargets.Class|
                  AttributeTargets.Struct|
                  AttributeTargets.Interface)]
  internal sealed class DeleteCctorAttribute : Attribute {
  }

  /// <summary>
  /// This attribute is placed on methods in override assemblies to delete the
  /// original method.  This shouldn't be used for optimization.  For example,
  /// this was introduced to temporarily remove a complex interface
  /// implementation that could not be handled by MethodHierarchy.
  /// </summary>
  [Information(InformationCategory.Override,
               "Delete the original method implementation.")]
  [AttributeUsage(AttributeTargets.Method)]
  public sealed class DeleteAttribute : Attribute {
  }

  [Information(InformationCategory.Override,
               "Used when an override type has a different StructLayout kind that the " +
               "original.  Specifies that the override layout kind is the one that should" +
               "be kept.")]
  [AttributeUsage(AttributeTargets.Struct)]
  public sealed class OverrideLayoutAttribute : Attribute {
  }

  [Information(InformationCategory.Override,
               "Used when an override method has a different accessibility " +
               "than the original.  Specifies that the override " +
               "accessibility is the one that should be kept.")]
  [AttributeUsage(AttributeTargets.Method)]
  public sealed class OverrideAccessibilityAttribute : Attribute {
  }

  // There are at least three reasons why one would need to prevent
  // the automatic insertion of vanilla reference-counting (RC) code
  // into the body of a method, property or constructor:
  //
  //     1. To suppress reference counting before a reference to
  //        the installed GC is set up.
  //
  //     2. Methods that directly manipulate reference counts such
  //        as allocation routines.
  //
  //     3. To suppress the insertion of RC code into code bodies
  //        that may be directly or indirectly invoked from the
  //        IncrementRefCount or DecrementRefCount methods of the
  //        reference-counting collector.
  //
  // The IrRCUpdate compiler phase can be made to skip code bodies for
  // any of the above reasons by affixing one of two special attributes
  // to their declarations. Currently, the [PreInitRefCounts] attribute
  // is used to mark code that could be invoked before the GC gets set
  // up and that, in its absence, may cause the IrRCUpdate phase to
  // insert RC increment and decrement code. The [ManualRefCounts]
  // attribute models cases in which the code writer takes the onus of
  // maintaining consistent reference counts.
  //
  // The reason for separating the preinitialization case from the
  // other two is because special RC updates, which test for
  // initialization of the GC before incrementing or decrementing the
  // reference counts, could still have been inserted into code bodies
  // marked as [PreInitRefCounts]. However, if the same code body is
  // called after initialization, such updates may slow down the
  // common case. This provides an optimization opportunity for the
  // compiler in which a method f marked with [PreInitRefCounts] could
  // be cloned into a version f' that contains plain RC code and that
  // is actually called wherever a non-[PreInitRefCounts] method such
  // as g calls f.
  //
  // If a method h has the [ManualRefCounts] attribute and if reference
  // counts are directly read or written in h, then the code must either
  // be also marked as [NoInline] or must only be called from methods
  // that also have the [ManualRefCounts] attribute. This is because if
  // h were inlined into a method in which reference counting is on by
  // default, the injected RC code may cause the reference counts
  // to become inconsistent.
  [Information(InformationCategory.Research,
               "Code may be invoked before the GC has been initialized.  Use increment/decrement " +
               "methods that check for GC initialization.")]
  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Property|
                  AttributeTargets.Constructor)]
  [RequiredByBartok]
  internal sealed class PreInitRefCountsAttribute: Attribute {
  }

  [Information(InformationCategory.Research,
               "Prevents the compiler from injecting calls to increment/decrement the " +
               "ref count.  This is used when the code manages the ref counts them explicitly.")]
  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Property|
                  AttributeTargets.Constructor)]
  [RequiredByBartok]
  internal sealed class ManualRefCountsAttribute: Attribute {
  }

  // This marks classes that are acyclic reference types.
  // (See IrAcyclicRefTypes.cs.)
  [Information(InformationCategory.Research,
               "This type will not appear in a reference cycle.")]
  [AttributeUsage(AttributeTargets.Class)]
  [RequiredByBartok]
  internal sealed class AcyclicRefTypeAttribute: Attribute {
  }

  [Information(InformationCategory.Research,
               "Prevents a null check when loading the field.")]
  [AttributeUsage(AttributeTargets.Field)]
  internal sealed class TrustedNonNullAttribute: Attribute {
  }

  // This attribute appears on definitions that need to be included in
  // mscorlibOverride sources to make the csharp compile work (because
  // they are referenced in those sources), but that aren't actually
  // intended to be overridden.
  [Information(InformationCategory.Override,
               "Placed on definitions that must appear in mscorlibOverride.  " +
               "These are not intended to be overridden, but must appear here " +
               "because they are referenced from within mscorlibOverride.")]
  public class AccessPointOnlyAttribute : Attribute {
  }
  
  [Information("Prevents the compiler from inserting GC read/write barriers.")]
  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Class|
                  AttributeTargets.Struct|
                  AttributeTargets.Constructor|
                  AttributeTargets.Field)]
  [RequiredByBartok]
  public sealed partial class NoBarriersAttribute: Attribute {
  }
  
  // Only applies for header fields.  Specifies that this header field must be
  // initialized to point at the object itself.  The runtime knows this and will
  // set this field accordingly, but the InstanceBuilder must be told using this
  // attribute.
  [Information("Specifies that a header field must be initialized to point at " +
               "the object itself.  Only applies to header fields initialized by " +
               "InstanceBuilder.")]
  [AttributeUsage(AttributeTargets.Field)]
  [RequiredByBartok]
  public sealed class SelfPointAttribute: Attribute {
  }
  
  // Only applies for header fields.  Specifies that the header field (which
  // must be an integer type) must be initialized to the given, if an object
  // containing the field is built by the compiler, inside of InstanceBuilder.
  [Information("Specifies that a header field (which must be an integer type) must be " +
               "initialized to the given value.  Only applies to header fields inititialized " +
               "by InstanceBuilder.")]
  [AttributeUsage(AttributeTargets.Field)]
  [RequiredByBartok]
  public sealed class CompilerInitFieldAttribute: Attribute {
      public CompilerInitFieldAttribute(long value) {}
  }
}

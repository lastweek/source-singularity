//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.Collections;
using System.IO;
using Bartok.DebugInfo;

namespace Bartok.MSIL
{

  public class MetaDataMethod: MetaDataObject {

      // Constructor Methods

      internal MetaDataMethod(int rva, short implFlags, short flags,
                              string name, Signature signature,
                              int paramIndex) {
          this.rva = rva;
          this.implFlags = implFlags;
          this.flags = flags;
          this.name = name;
          this.signature = signature;
          this.paramIndex = paramIndex;
      }

      // These are technically not constructor methods, but they are meant to
      // be used to set up the object

      internal void AddGenericParam(MetaDataGenericParam genericParam) {
          if (this.genericParamList == null) {
              this.genericParamList = new ArrayList(2);
          }

          if (genericParam.Number != this.genericParamList.Count) {
              throw new MetaDataLoader.IllegalMetaDataFormatException
                  ("Generic parameters out of order - is this allowed?");
          }

          this.genericParamList.Add(genericParam);
      }

      internal void registerReferences(int paramCount,
                                       MetaDataMethod[] paramOwners) {
          if (this.paramIndex <= paramCount) {
              paramOwners[this.paramIndex] = this;
          }
      }

      internal void resolveReferences(MetaDataLoader loader,
                                      MetaDataMethod[] paramOwners) {
          this.signature = signature.resolve(loader);
          // paramOwners[paramOwners.Length-1] == null, so this is safe
          int paramEndIndex = this.paramIndex;
          while (paramOwners[paramEndIndex] == this) {
              paramEndIndex++;
          }
          int paramCount = paramEndIndex - this.paramIndex;
          this.paramArray = loader.getParams(this.paramIndex, paramCount);
          int limit = this.paramArray.Length;
          if (paramCount != limit) {
              MetaDataParam resultParam = loader.getParam(this.paramIndex);
              resultParam.resolveReferences(this);
          }
          for (int i = 0; i < limit; i++) {
              this.paramArray[i].resolveReferences(this);
          }
      }

      internal void loadInstructions(MetaDataLoader mdLoader,
                                     PELoader peLoader,
                                     Stream fileStream,
                                     int[] lines,
                                     int[] columns,
                                     int[] offsets,
                                     String srcFileName,
                                     int count) {
          if (this.rva != 0) {
              if ((this.flags & (short) MethodAttributes.PinvokeImpl) == 0 ||
                  (this.flags & (short) MethodAttributes.UnmanagedExport) != 0) {
                  int codeOffset = peLoader.VaToOffset(rva);
                  this.instructions =
                      Instruction.getInstructions(mdLoader, fileStream,
                                                  codeOffset, lines, columns,
                                                  offsets, srcFileName, count,
                                                  out this.ehTable,
                                                  out this.bbTable,
                                                  out this.maxStack,
                                                  out this.locals,
                                                  out this.initLocals);
              }
              else {
                  Console.WriteLine("Not loading embedded native code for "+
                                    this);
              }
          }
      }

      internal void setParent(MetaDataTypeDefinition parent) {
          this.parent = parent;
      }

      // Access Methods

      // of MetaDataGenericParam
      public ArrayList GenericParamList {
          get {
              return this.genericParamList;
          }
      }

      public Instruction[] Instructions {
          get {
              return this.instructions;
          }
      }

      public EHClause[] EHTable {
          get {
              return this.ehTable;
          }
      }

      // An array of basic block start indices in "Instructions"
      public int[] BBTable {
          get {
              return this.bbTable;
          }
      }

      public int MaxStack {
          get {
              return this.maxStack;
          }
      }

      public Signature.Type[] Locals {
          get {
              return this.locals;
          }
      }

      // Bitmask described by MethodImplAttributes
      public short ImplFlags {
          get {
              return this.implFlags;
          }
      }

      // Bitmask described by MethodAttributes
      public short Flags {
          get {
              return this.flags;
          }
      }

      public string FullName {
          get {
              if (this.parent != null) {
                  return this.parent.FullName + "." + this.Name;
              }
              else {
                  return this.Name;
              }
          }
      }


      public string Name {
          get {
              return this.name;
          }
      }

      public SignatureMethod Signature {
          get {
              return (SignatureMethod) this.signature;
          }
      }

      public MetaDataParam[] Parameters {
          get {
              return this.paramArray;
          }
      }

      public MetaDataTypeDefinition Parent {
          get {
              return this.parent;
          }
      }

      public int Rva {
          get { return rva; }
      }

      public bool IsEmpty {
          get { return isEmpty; }
          set { isEmpty = value; }
      }

      public bool InitLocals {
          get { return initLocals; }
      }

      public DebugLineNumber BaseLineNumber {
          get { return baseLineNumber; }
          set { baseLineNumber = value; }
      }

      public DebugLineNumber LastLineNumber {
          get { return lastLineNumber; }
          set { lastLineNumber = value; }
      }

      public int NumOfLines {
          get { return numOfLines; }
          set { numOfLines = value; }
      }

      public String SrcFileName {
          get { return srcFileName; }
          set { srcFileName = value; }
      }

      public bool HasDebugInfo {
          get { return hasDebugInfo; }
          set { hasDebugInfo = value; }
      }

      public String[] LocalVarNames {
          get { return localVarNames; }
          set { localVarNames = value; }
      }

      // Debug Methods

      public override string ToString() {
          return ("MetaDataMethod("+this.FullName+")");
      }

      public override string ToStringLong() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataMethod(");
          if (this.genericParamList != null
              && this.genericParamList.Count > 0) {
              sb.Append("GenericParams<");
              foreach (MetaDataGenericParam param in this.genericParamList) {
                  sb.Append(param.ToString());
                  sb.Append(",");
              }
              sb.Remove(sb.Length-1, 1);
              sb.Append(">,");
          }
          sb.Append(this.rva);
          sb.Append(",");
          sb.Append(this.implFlags.ToString("x"));
          sb.Append(",");
          sb.Append(this.flags.ToString("x"));
          sb.Append(",");
          if (this.parent != null) {
              sb.Append(this.parent.FullName);
              sb.Append(".");
          }
          sb.Append(this.name);
          sb.Append(",");
          sb.Append(this.signature);
          sb.Append(",");
          if (this.paramArray == null) {
              sb.Append(this.paramIndex);
          }
          else if (this.paramArray.Length == 0) {
              sb.Append("No parameters");
          }
          else {
              sb.Append("parameters(");
              foreach (MetaDataParam param in this.paramArray) {
                  sb.Append(param.ToString());
                  sb.Append(",");
              }
              sb.Remove(sb.Length-1, 1);
              sb.Append(")");
          }
          sb.Append(")");
          return sb.ToString();
      }

      // State

      private readonly int                    rva;
      private          ArrayList              genericParamList;
      private          Instruction[]          instructions;
      private          EHClause[]             ehTable;
      private          int[]                  bbTable;
      private          int                    maxStack;
      private          Signature.Type[]       locals;
      private readonly short                  implFlags;
      private readonly short                  flags;
      private readonly string                 name;
      private          Signature              signature;
      private readonly int                    paramIndex;
      private          MetaDataParam[]        paramArray;
      private          MetaDataTypeDefinition parent;
      private          bool                   isEmpty;
      private          bool                   initLocals;

      // information for debugging
      private DebugLineNumber  baseLineNumber;
      private DebugLineNumber lastLineNumber;
      private int numOfLines;
      private String srcFileName;
      private bool hasDebugInfo;
      private String[] localVarNames;

      // Internal Classes

      // Section 22.1.7 of ECMA spec, Section II
      public enum MethodImplAttributes
      {
          // code impl mask
          CodeTypeMask         = 0x0003, // Flags about code type.
              IL               = 0x0000, // Method impl is IL.
              Native           = 0x0001, // Method impl is native.
              OPTIL            = 0x0002, // Method impl is OPTIL
              Runtime          = 0x0003, // Method impl is provided by the runtime.
              // managed mask
              ManagedMask      = 0x0004, // Flags specifying whether the code is managed or unmanaged.
              Unmanaged        = 0x0004, // Method impl is unmanaged, otherwise managed.
              Managed          = 0x0000, // Method impl is managed.
              // implementation info and interop
              ForwardRef       = 0x0010, // Indicates method is defined; used primarily in merge scenarios.
              PreserveSig      = 0x0080, // Indicates method sig is not to be mangled to do HRESULT conversion.
              InternalCall     = 0x1000, // Reserved for internal use.
              Synchronized     = 0x0020, // Method is single threaded through the body.
              NoInlining       = 0x0008, // Method may not be inlined.
              MaxMethodImplVal = 0xffff // Range check value
      }

      public enum MethodAttributes {
          // member access attributes
          MemberAccessMask     = 0x0007, // Use this mask to retrieve accessibility information.
              PrivateScope     = 0x0000, // Member not referenceable.
              Private          = 0x0001, // Accessible only by the parent type.
              FamANDAssem      = 0x0002, // Accessible by sub-types only in this Assembly.
              Assem            = 0x0003, // Accessibly by anyone in the Assembly.
              Family           = 0x0004, // Accessible only by type and sub-types.
              FamORAssem       = 0x0005, // Accessibly by sub-types anywhere, plus anyone in assembly.
              Public           = 0x0006, // Accessibly by anyone who has visibility to this scope.
              // method contract attributes.
              Static           = 0x0010, // Defined on type, else per instance.
              Final            = 0x0020, // Method may not be overridden.
              Virtual          = 0x0040, // Method virtual.
              HideBySig        = 0x0080, // Method hides by name+sig, else just by name.
              // vtable layout mask - Use this mask to retrieve vtable attributes.
              VtableLayoutMask = 0x0100,
              ReuseSlot        = 0x0000, // The default.
              NewSlot          = 0x0100, // Method always gets a new slot in the vtable.
              // method implementation attributes.
              Abstract         = 0x0400, // Method does not provide an implementation.
              SpecialName      = 0x0800, // Method is special.  Name describes how.
              // interop attributes
              PinvokeImpl      = 0x2000, // Implementation is forwarded through pinvoke.
              UnmanagedExport  = 0x0008, // Managed method exported via thunk to unmanaged code.
              // Reserved flags for runtime use only.
              ReservedMask     = 0xd000,
              RTSpecialName    = 0x1000, // Runtime should check name encoding.
              HasSecurity      = 0x4000, // Method has security associate with it.
              RequireSecObject = 0x8000 // Method calls another method containing security code.
      }

  }

}

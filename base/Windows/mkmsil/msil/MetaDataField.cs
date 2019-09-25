// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;

  public class MetaDataField: MetaDataObject {

      // Constructor Methods

      internal MetaDataField(short flags, string name, Signature signature) {
          this.flags = flags;
          this.name = name;
          this.signature = signature;
      }

      internal void resolveReferences(MetaDataLoader loader) {
          this.signature = this.signature.resolve(loader);
      }

      internal void resolveReferences(MetaDataTypeDefinition parent) {
          this.parent = parent;
      }

      internal void resolveReferences(MetaDataFieldRVA fieldRVA) {
          this.fieldRVA = fieldRVA;
      }

      internal void resolveReferences(MetaDataConstant constant) {
          this.constant = constant;
      }

      internal void resolveReferences(MetaDataFieldLayout fieldLayout) {
          this.layout = fieldLayout;
      }

      // Access Methods

      // Bitmask described by FieldAttributes
      public int Flags {
          get {
              return this.flags;
          }
      }

      public string Name {
          get {
              return this.name;
          }
      }

      public SignatureField Signature {
          get {
              return (SignatureField) this.signature;
          }
      }

      public MetaDataTypeDefinition Parent {
          get {
              return this.parent;
          }
      }

      public Object DefaultValue {
          get {
              if ((this.flags & (int) FieldAttributes.HasDefault) != 0 &&
                  this.constant != null) {
                  return this.constant.Value;
              }
              else if ((this.flags & (int) FieldAttributes.HasFieldRVA) != 0 &&
                         this.fieldRVA != null) {
                  return this.fieldRVA.DataBytes;
              }
              else {
                  return null;
              }
          }
      }

      public int RVA {
          get {
              if ((this.flags & (int) FieldAttributes.HasFieldRVA) != 0 &&
                  this.fieldRVA != null) {
                  return this.fieldRVA.RVA;
              }
              else {
                  return 0;
              }
          }
      }

      public MetaDataFieldLayout Layout {
          get {
              return this.layout;
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataField("+this.flags.ToString("x4")+","+
                  this.name+","+this.signature+")");
      }

      public override String ToStringLong() {
          return ("MetaDataField("+this.flags.ToString("x4")+","+
                  this.parent.FullName+"."+this.name+","+this.signature+
                  ((this.DefaultValue!=null)?("["+this.DefaultValue+"]"):"")+
                  ")");
      }

      // State

      private readonly int                    flags;
      private readonly string                 name;
      private          Signature              signature;
      private          MetaDataTypeDefinition parent;
      private          MetaDataFieldRVA       fieldRVA;
      private          MetaDataConstant       constant;
      private          MetaDataFieldLayout    layout;

      // Internal Classes

      // Section 22.1.3 of ECMA spec, Section II
      public enum FieldAttributes {
          // member access mask - Use this mask to retrieve accessibility information.
          FieldAccessMask     = 0x0007,
              PrivateScope    = 0x0000, // Member not referenceable.
              Private         = 0x0001, // Accessible only by the parent type.  
              FamANDAssem     = 0x0002, // Accessible by sub-types only in this Assembly.
              Assembly        = 0x0003, // Accessibly by anyone in the Assembly.
              Family          = 0x0004, // Accessible only by type and sub-types.    
              FamORAssem      = 0x0005, // Accessibly by sub-types anywhere, plus anyone in assembly.
              Public          = 0x0006, // Accessibly by anyone who has visibility to this scope.    
              // end member access mask
              // field contract attributes.
              Static          = 0x0010, // Defined on type, else per instance.
              InitOnly        = 0x0020, // Field may only be initialized, not written to after init.
              Literal         = 0x0040, // Value is compile time constant.
              NotSerialized   = 0x0080, // Field does not have to be serialized when type is remoted.
              SpecialName     = 0x0200, // field is special.  Name describes how.
              // interop attributes
              PinvokeImpl     = 0x2000,// Implementation is forwarded through pinvoke.
              // Reserved flags for runtime use only.
              ReservedMask    = 0x9500,
              RTSpecialName   = 0x0400, // Runtime(metadata internal APIs) should check name encoding.
              HasFieldMarshal = 0x1000, // Field has marshalling information.
              HasDefault      = 0x8000, // Field has default.
              HasFieldRVA     = 0x0100  // Field has RVA.
      }

  }

}

// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataParam: MetaDataObject {

      // Constructor Methods

      internal MetaDataParam(short flags, short sequence, String name) {
          this.flags = flags;
          this.sequence = sequence;
          this.name = name;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataMethod parent) {
          this.parent = parent;
      }

      internal void resolveReferences(MetaDataConstant constant) {
          this.constant = constant;
      }

      // Access Methods

      // Bitmask described by ParamAttributes
      public short Flags {
          get {
              return this.flags;
          }
      }

      public short Sequence {
          get {
              return this.sequence;
          }
      }

      public String Name {
          get {
              return this.name;
          }
      }

      public MetaDataMethod Parent {
          get {
              return this.parent;
          }
      }

      public Object DefaultValue {
          get {
              if ((this.flags & (int) ParamAttributes.HasDefault) != 0) {
                  return this.constant.Value;
              }
              else {
                  return null;
              }
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataParam("+this.name+")");
      }

      public override String ToStringLong() {
          return ("MetaDataParam("+this.flags.ToString("x")+","+this.sequence+
                  ","+this.name+"<"+this.parent+">)");
      }

      // State

      private readonly short   flags;
      private readonly short   sequence;
      private readonly String  name;
      private MetaDataMethod   parent;
      private MetaDataConstant constant;

      // Internal Classes

      // Section 22.1.9 of ECMA spec, Section II
      // also found in Lightning\Src\inc\CorHdr.h
      public enum ParamAttributes {
          In                  =   0x0001, // Param is [In]    
              Out             =   0x0002, // Param is [out]   
              Optional        =   0x0010, // Param is optional    
              // Reserved flags for Runtime use only.
              ReservedMask    =   0xf000,
              HasDefault      =   0x1000, // Param has default value.
              HasFieldMarshal =   0x2000, // Param has FieldMarshal.
              Unused          =   0xcfe0
      }

  }

}

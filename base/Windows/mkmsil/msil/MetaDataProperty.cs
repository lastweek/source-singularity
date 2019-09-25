//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataProperty: MetaDataObject {

      // Constructor Methods

      internal MetaDataProperty(short flags, String name, Signature type) {
          this.flags = flags;
          this.name = name;
          this.type = type;
      }

      internal void resolveReferences(MetaDataLoader loader) {
          this.type = this.type.resolve(loader);
      }

      internal void resolveReferences(MetaDataConstant constant) {
          this.constant = constant;
      }

      // Access Methods

      // Bitmask described by PropertyAttributes
      public short Flags {
          get {
              return this.flags;
          }
      }

      public String Name {
          get {
              return this.name;
          }
      }

      public Signature Type {
          get {
              return this.type;
          }
      }

      public Object DefaultValue {
          get {
              if ((this.flags & (int) PropertyAttributes.HasDefault) != 0) {
                  return this.constant.Value;
              }
              else {
                  return null;
              }
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataProperty("+this.flags.ToString("x")+","+this.name+
                  ","+this.type+")");
      }

      // State

      private readonly short            flags;
      private readonly String           name;
      private          Signature        type;
      private          MetaDataConstant constant;

      // Internal Classes

      // 22.1.10
      public enum PropertyAttributes {
          SpecialName        = 0x0200, // property is special.  Name describes how.
              // Reserved flags for Runtime use only.
              ReservedMask   = 0xf400,
              RTSpecialName  = 0x0400, // Runtime(metadata internal APIs) should check name encoding.
              HasDefault     = 0x1000, // Property has default
              Unused         = 0xe9ff
      }

  }

}

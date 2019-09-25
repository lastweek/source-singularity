//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;
  using System.Collections;

  public class MetaDataGenericParam: MetaDataObject {

      // Constructor Methods

      internal MetaDataGenericParam(short number, short flags, int ownerIndex,
                                    String name, int kind)
      {
          this.number = number;
          this.flags = flags;
          this.ownerIndex = ownerIndex;
          this.name = name;
          this.kind = kind;
      }

      internal void AddGenericParamConstraint(MetaDataObject constraint) {
          if (this.genericParamConstraints == null) {
              this.genericParamConstraints = new ArrayList(2);
          }
          this.genericParamConstraints.Add(constraint);
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.owner = loader.getTypeOrMethodDef(this.ownerIndex);

          if (this.owner is MetaDataTypeDefinition) {
              ((MetaDataTypeDefinition) this.owner).AddGenericParam(this);
          }
          else if (this.owner is MetaDataMethod) {
              ((MetaDataMethod) this.owner).AddGenericParam(this);
          }
          else {
              throw new MetaDataLoader.IllegalMetaDataFormatException
                  ("Unknown owner of GenericParam");
          }
      }

      // Access Methods

      public short Number {
          get {
              return this.number;
          }
      }

      // Bitmask described by GenericParamAttributes
      public short Flags {
          get {
              return this.flags;
          }
      }

      // TypeOrMethodDef
      public MetaDataObject Owner {
          get {
              return this.owner;
          }
      }

      public String Name {
          get {
              return this.name;
          }
      }

      public int Kind {
          get {
              return this.kind;
          }
      }

      // of TypeDefOrRef
      public ArrayList GenericParamConstraints {
          get {
              return this.genericParamConstraints;
          }
      }

      // Debug Methods

      public override String ToString() {
          return "MetaDataGenericParam("+this.name+")";
      }

      public override String ToStringLong() {
          return "MetaDataGenericParam("+this.number+","+
              this.flags.ToString("x")+","+this.ownerIndex.ToString("x")+","+
              this.name+","+this.kind+")";
      }

      // State

      private readonly short number;
      private readonly short flags;
      private readonly int ownerIndex;
      private          MetaDataObject owner;
      private readonly String name;
      private readonly int kind;

      private ArrayList genericParamConstraints;

      // Internal Classes

      // Section 23.1.7 of ECMA spec, Section II
      // "Flags for Generic Parameters [GenericParamAttributes]"
      // N.B. I think these are for future use
      public enum GenericParamAttributes {
          VarianceMask  = 0x0003,
          NonVariant    = 0x0000, // The generic parameter is non-variant
          Covariant     = 0x0001, // The generic parameter is covariant
          Contravariant = 0x0002  // The generic parameter is contravariant
      }
  }
}

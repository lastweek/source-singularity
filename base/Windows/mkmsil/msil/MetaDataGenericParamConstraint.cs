//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;
  using System.Collections;

  public class MetaDataGenericParamConstraint: MetaDataObject {
      // Constructor Methods

      internal MetaDataGenericParamConstraint(int ownerIndex,
                                              int constraintIndex)
      {
          this.ownerIndex = ownerIndex;
          this.constraintIndex = constraintIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.owner = loader.getGenericParam(this.ownerIndex);
          this.constraint = loader.getTypeDefOrRef(this.constraintIndex);
          this.owner.AddGenericParamConstraint(this.constraint);
      }

      // Access Methods

      public MetaDataGenericParam Owner {
          get {
              return this.owner;
          }
      }

      // TypeDefOrRef
      public MetaDataObject Constraint {
          get {
              return this.constraint;
          }
      }

      // Debug Methods

      public override String ToString() {
          return "MetaDataGenericParamContraint("+this.constraint+")";
      }

      public override String ToStringLong() {
          return "MetaDataGenericParamContraint("+this.ownerIndex+","+
              this.ownerIndex+","+this.constraintIndex+","+this.constraint+")";
      }

      // State

      private readonly int ownerIndex;
      private          MetaDataGenericParam owner;
      private readonly int constraintIndex;
      private          MetaDataObject constraint;
  }
}

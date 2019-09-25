// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataPropertyPtr: MetaDataObject {

      // Constructor Methods

      internal MetaDataPropertyPtr(int propertyIndex) {
          this.propertyIndex = propertyIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.property = loader.getProperty(this.propertyIndex);
      }

      // Access Methods

      public MetaDataProperty Property {
          get {
              return this.property;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.property == null) {
              return "MetaDataPropertyPtr("+this.propertyIndex+")";
          }
          else {
              return "MetaDataPropertyPtr("+this.property+")";
          }
      }

      // State

      private readonly int              propertyIndex;
      private          MetaDataProperty property;

  }

}

// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataPropertyMap: MetaDataObject {

      // Constructor Methods

      internal MetaDataPropertyMap(int parentIndex, int propertyIndex) {
          this.parentIndex = parentIndex;
          this.propertyIndex = propertyIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.parent = loader.getTypeDef(this.parentIndex);
          this.property = loader.getProperty(this.propertyIndex);
      }

      // Access Methods

      public MetaDataTypeDefinition Parent {
          get {
              return this.parent;
          }
      }

      public MetaDataProperty Property {
          get {
              return this.property;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.parent == null || this.property == null) {
              return ("MetaDataPropertyMap("+this.parentIndex+","+
                      this.propertyIndex+")");
          }
          else {
              return "MetaDataPropertyMap("+this.parent+","+this.property+")";
          }
      }

      // State

      private readonly int                    parentIndex;
      private          MetaDataTypeDefinition parent;
      private readonly int                    propertyIndex;
      private          MetaDataProperty       property;

  }

}

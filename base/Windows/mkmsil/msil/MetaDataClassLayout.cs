// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataClassLayout: MetaDataObject {

      // Constructor Methods

      internal MetaDataClassLayout(short packingSize, int classSize,
                                   int parentIndex) {
          this.packingSize = packingSize;
          this.classSize = classSize;
          this.parentIndex = parentIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.parent = loader.getTypeDef(this.parentIndex);
          this.parent.resolveReferences(this);
      }

      // Access Methods

      public short PackingSize {
          get {
              return this.packingSize;
          }
      }

      public int ClassSize {
          get {
              return this.classSize;
          }
      }

      public MetaDataTypeDefinition Parent {
          get {
              return this.parent;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.parent == null) {
              return ("MetaDataClassLayout("+this.packingSize+","+
                      this.classSize+","+this.parentIndex+")");
          }
          else {
              return ("MetaDataClassLayout("+this.packingSize+","+
                      this.classSize+","+this.parent+")");
          }
      }

      // State

      private readonly short                  packingSize;
      private readonly int                    classSize;
      private readonly int                    parentIndex;
      private          MetaDataTypeDefinition parent;

  }

}

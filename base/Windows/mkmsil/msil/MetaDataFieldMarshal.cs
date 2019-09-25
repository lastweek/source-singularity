// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataFieldMarshal: MetaDataObject {

      // Constructor Methods

      internal MetaDataFieldMarshal(int parentIndex, MarshalSpec nativeType) {
          this.parentIndex = parentIndex;
          this.nativeType = nativeType;
      }

      internal void resolveReferences(MetaDataLoader loader) {
          this.parent = loader.getHasFieldMarshal(this.parentIndex);
      }

      // Access Methods

      public MetaDataObject Parent {
          get {
              return this.parent;
          }
      }

      public MarshalSpec NativeType {
          get {
              return this.nativeType;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.parent == null) {
              return ("MetaDataFieldMarshal("+this.parentIndex+","+
                      this.nativeType+")");
          }
          else {
              return ("MetaDataFieldMarshal("+this.parent.ToStringLong()+","+
                      this.nativeType+")");
          }
      }

      // State

      private readonly int            parentIndex;
      private          MetaDataObject parent;
      private readonly MarshalSpec    nativeType;
  }

}

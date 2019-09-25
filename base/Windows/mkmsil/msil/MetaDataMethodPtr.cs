// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataMethodPtr: MetaDataObject {

      // Constructor Methods

      internal MetaDataMethodPtr(int methodIndex) {
          this.methodIndex = methodIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.method = loader.getMethod(this.methodIndex);
      }

      // Access Methods

      public MetaDataMethod Method {
          get {
              return this.method;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.method == null) {
              return "MetaDataMethodPtr("+this.methodIndex+")";
          }
          else {
              return "MetaDataMethodPtr("+this.method+")";
          }
      }

      // State

      private readonly int            methodIndex;
      private          MetaDataMethod method;

  }

}

// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataParamPtr: MetaDataObject {

      // Constructor Methods

      internal MetaDataParamPtr(int paramIndex) {
          this.paramIndex = paramIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.param = loader.getParam(this.paramIndex);
      }

      // Access Methods

      public MetaDataParam Parameter {
          get {
              return this.param;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.param == null) {
              return "MetaDataParamPtr("+this.paramIndex+")";
          }
          else {
              return "MetaDataParamPtr("+this.param+")";
          }
      }

      // State

      private readonly int           paramIndex;
      private          MetaDataParam param;

  }

}

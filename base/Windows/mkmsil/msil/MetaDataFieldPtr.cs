// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.IO;

namespace Bartok.MSIL
{

  public class MetaDataFieldPtr: MetaDataObject {

      // Constructor Methods

      internal MetaDataFieldPtr(int fieldIndex) {
          this.fieldIndex = fieldIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.field = loader.getField(this.fieldIndex);
      }

      // Access Methods

      public MetaDataField Field {
          get {
              return this.field;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.field == null) {
              return "MetaDataFieldPtr("+this.fieldIndex+")";
          }
          else {
              return "MetaDataFieldPtr("+this.field+")";
          }
      }

      // State

      private int fieldIndex;
      private MetaDataField field;

  }

}

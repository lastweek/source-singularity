// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataFieldLayout: MetaDataObject {

      // Constructor Methods

      internal MetaDataFieldLayout(int offset, MetaDataField field) {
          this.offset = offset;
          this.field = field;
      }

      // Access Methods

      public int Offset {
          get {
              return this.offset;
          }
      }

      public MetaDataField Field {
          get {
              return this.field;
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataFieldLayout("+this.offset+","+this.field+")");
      }

      // State

      private readonly int           offset;
      private readonly MetaDataField field;

  }

}

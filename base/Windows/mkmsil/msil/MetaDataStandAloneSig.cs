// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataStandAloneSig: MetaDataObject {

      // Constructor Methods

      internal MetaDataStandAloneSig(Signature signature) {
          this.signature = signature;
      }

      internal void resolveReferences(MetaDataLoader loader) {
          this.signature = this.signature.resolve(loader);
      }

      // Access Methods

      public Signature Signature {
          get {
              return this.signature;
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataStandAloneSig("+this.signature+")");
      }

      // State

      private Signature signature;

  }

}

// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataTypeSpec: MetaDataObject {

      // Constructor Methods

      internal MetaDataTypeSpec(Signature signature) {
          this.signature = signature;
      }

      internal void resolveReferences(MetaDataLoader loader) {
          this.signature = signature.resolveTypeSpec(loader);
      }

      // Access Methods

      public SignatureTypeSpec Signature {
          get {
              return (SignatureTypeSpec) this.signature;
          }
      }

      // Debug Methods

      public override String ToString() {
          return "MetaDataTypeSpec("+this.signature+")";
      }

      // State

      private Signature signature;

  }

}

// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class SignatureTypeSpec: Signature {

      // Constructor Methods

      internal SignatureTypeSpec(Type type) {
          this.type = type;
      }

      // Access Methods

      public Type TypeSpecType {
          get { return type; }
      }

      // Debug Methods

      public override String ToString() {
          return "SignatureTypeSpec("+this.type+")";
      }

      // State

      private readonly Type type;

  }

}

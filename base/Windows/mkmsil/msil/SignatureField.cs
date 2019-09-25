// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class SignatureField: Signature {

      // Constructor Methods

      internal SignatureField(Type type) {
          this.type = type;
      }

      // Access Methods

      public Type FieldType {
          get {
              return this.type;
          }
      }

      // Debug Methods

      public override String ToString() {
          return "SignatureField("+type+")";
      }

      // State

      private readonly Type type;

  }

}

// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class SignatureLocalVar: Signature {

      // Constructor Methods

      internal SignatureLocalVar(Type[] locals) {
          this.locals = locals;
      }

      // Access Methods

      public Type[] Locals {
          get {
              return this.locals;
          }
      }

      // Debug Methods

      public override String ToString() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("SignatureLocalVar(");
          if (locals.Length > 0) {
              sb.Append(locals[0]);
              for (int i = 1; i < locals.Length; i++) {
                  sb.Append(",");
                  sb.Append(locals[i]);
              }
          }
          sb.Append(")");
          return sb.ToString();
      }

      // State

      private readonly Type[] locals;

  }

}

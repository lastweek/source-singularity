// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class SignatureProperty: Signature {

      // Constructor Methods

      internal SignatureProperty(Type returnType,
                                 Param[] parameters) {
          this.returnType = returnType;
          this.parameters = parameters;
      }

      // Access Methods

      // Debug Methods

      // State

      private readonly Type returnType;
      private readonly Param[] parameters;

  }

}

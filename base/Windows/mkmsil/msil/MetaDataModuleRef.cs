// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataModuleRef: MetaDataObject {

      // Constructor Methods

      internal MetaDataModuleRef(String name) {
          this.name = name;
      }

      // Access Methods

      public String Name {
          get {
              return this.name;
          }
      }

      // Debug Methods

      public override String ToString() {
          return "MetaDataModuleRef("+this.name+")";
      }

      // State

      private readonly String name;

  }

}

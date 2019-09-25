// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataAssemblyProcessor: MetaDataObject {

      // Constructor Methods

      internal MetaDataAssemblyProcessor(int processor) {
          this.processor = processor;
      }

      // Access Methods

      public int Processor {
          get {
              return this.processor;
          }
      }

      // Debug Methods

      public override String ToString() {
          return "MetaDataAssemblyProcessor("+this.processor+")";
      }

      // State

      private readonly int processor;

  }

}

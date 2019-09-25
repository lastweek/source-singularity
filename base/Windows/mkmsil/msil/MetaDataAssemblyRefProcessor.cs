// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataAssemblyRefProcessor: MetaDataObject {

      // Constructor Methods

      internal MetaDataAssemblyRefProcessor(int processor,
                                            MetaDataAssemblyRef assemblyRef) {
          this.processor = processor;
          this.assemblyRef = assemblyRef;
      }

      // Access Methods

      public int Processor {
          get {
              return this.processor;
          }
      }

      public MetaDataAssemblyRef AssemblyRef {
          get {
              return this.assemblyRef;
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataAssemblyRefProcessor("+this.processor+","+
                  this.assemblyRef+")");
      }

      // State

      private readonly int                 processor;
      private readonly MetaDataAssemblyRef assemblyRef;

  }

}

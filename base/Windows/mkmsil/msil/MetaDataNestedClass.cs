// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataNestedClass: MetaDataObject {

      // Constructor Methods

      internal MetaDataNestedClass(MetaDataTypeDefinition nestedClass,
                                   MetaDataTypeDefinition enclosingClass) {
          this.nestedClass = nestedClass;
          this.enclosingClass = enclosingClass;
      }

      // Access Methods

      public MetaDataTypeDefinition NestedClass {
          get {
              return this.nestedClass;
          }
      }

      public MetaDataTypeDefinition EnclosingClass {
          get {
              return this.enclosingClass;
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataNestedClass("+this.nestedClass+","+
                  this.enclosingClass+")");
      }

      // State

      private readonly MetaDataTypeDefinition nestedClass;
      private readonly MetaDataTypeDefinition enclosingClass;

  }

}

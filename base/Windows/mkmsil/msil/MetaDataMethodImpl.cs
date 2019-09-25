// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataMethodImpl: MetaDataObject {

      // Constructor Methods

      internal MetaDataMethodImpl(int classIndex, int bodyIndex,
                                  int declarationIndex) {
          this.classIndex = classIndex;
          this.bodyIndex = bodyIndex;
          this.declarationIndex = declarationIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.classObject = loader.getTypeDef(this.classIndex);
          this.body = loader.getMethodDefOrRef(this.bodyIndex);
          this.declaration = loader.getMethodDefOrRef(this.declarationIndex);
      }

      // Access Methods

      public MetaDataTypeDefinition Class {
          get {
              return this.classObject;
          }
      }

      public MetaDataObject Body {
          get {
              return this.body;
          }
      }

      public MetaDataObject Declaration {
          get {
              return this.declaration;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.classObject == null ||
              this.body == null ||
              this.declaration == null) {
              return ("MetaDataMethodImpl("+this.classIndex+","+
                      this.bodyIndex+","+this.declarationIndex+")");
          }
          else {
              return ("MetaDataMethodImpl("+this.classObject+","+this.body+","+
                      this.declaration+")");
          }
      }

      // State

      private readonly int                    classIndex;
      private          MetaDataTypeDefinition classObject;
      private readonly int                    bodyIndex;
      private          MetaDataObject         body;
      private readonly int                    declarationIndex;
      private          MetaDataObject         declaration;

      // Internal Classes

  }

}

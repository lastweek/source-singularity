// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;
  using System.Collections;

  public class MetaDataInterfaceImpl: MetaDataObject {

      // Constructor Methods

      internal MetaDataInterfaceImpl(int classIndex, int interfaceIndex) {
          this.classIndex = classIndex;
          this.interfaceIndex = interfaceIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader,
                                      ArrayList[] interfaceListArray) {
          this.classObject = loader.getTypeDef(this.classIndex);
          this.interfaceObject = loader.getTypeDefOrRef(this.interfaceIndex);
          if (interfaceListArray[this.classIndex] == null) {
              interfaceListArray[this.classIndex] = new ArrayList();
          }
          interfaceListArray[this.classIndex].Add(this.interfaceObject);
      }

      // Access Methods

      public MetaDataTypeDefinition Class {
          get {
              return this.classObject;
          }
      }

      public MetaDataObject Interface {
          get {
              return this.interfaceObject;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.classObject == null || this.interfaceObject == null) {
              return ("MetaDataInterfaceImpl("+this.classIndex+","+
                      this.interfaceIndex+")");
          }
          else {
              return ("MetaDataInterfaceImpl("+this.classObject+","+
                      this.interfaceObject+")");
          }
      }

      // State

      private readonly int                    classIndex;
      private          MetaDataTypeDefinition classObject;
      private readonly int                    interfaceIndex;
      private          MetaDataObject         interfaceObject;

  }

}

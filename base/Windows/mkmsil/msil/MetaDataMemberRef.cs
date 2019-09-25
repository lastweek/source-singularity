// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataMemberRef: MetaDataObject {

      // Constructor Methods

      internal MetaDataMemberRef(int classIndex, String name,
                                 Signature signature) {
          this.classIndex = classIndex;
          this.name = name;
          this.signature = signature;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.classObject = loader.getMemberRefParent(this.classIndex);
          this.signature = signature.resolve(loader);
      }

      // Access Methods

      // Returns one of MetaData{TypeDef,TypeRef,ModuleRef,MethodDef,TypeSpec}
      public MetaDataObject Class {
          get {
              return this.classObject;
          }
      }

      public String Name {
          get {
              return this.name;
          }
      }

      public Signature Signature {
          get {
              return this.signature;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.classObject == null) {
              return ("MetaDataMemberRef("+this.classIndex+","+this.name+","+
                  this.signature+")");
          }
          else {
              return ("MetaDataMemberRef("+this.classObject+","+this.name+","+
                      this.signature+")");
          }
      }

      // State

      private readonly int            classIndex;
      private          MetaDataObject classObject;
      private readonly String         name;
      private          Signature      signature;

  }

}

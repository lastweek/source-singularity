// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataExportedType: MetaDataObject {

      // Constructor Methods

      internal MetaDataExportedType(int flags, int typeDefId,
                                    String typeName, String typeNamespace,
                                    int implementationIndex) {
          this.flags = flags;
          this.typeDefId = typeDefId;
          this.typeName = typeName;
          this.typeNamespace = typeNamespace;
          this.implementationIndex = implementationIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          // Do not resolve the typeDef, as it may live in another file!
          // this.typeDef = loader.getTypeDef(this.typeDefId);
          this.implementation =
              loader.getImplementation(this.implementationIndex);
      }

      // Access Methods

      public int Flags {
          get {
              return this.flags;
          }
      }

      public MetaDataTypeDefinition TypeDefinition {
          get {
              return this.typeDef;
          }
          set {
              this.typeDef = value;
          }
      }

      public String Name {
          get {
              return this.typeName;
          }
      }

      public String Namespace {
          get {
              return this.typeNamespace;
          }
      }

      public MetaDataObject Implementation {
          get {
              return this.implementation;
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataExportedType("+
                  this.typeNamespace+"."+this.typeName+")");
      }

      public override String ToStringLong() {
          if (this.typeDef == null || this.implementation == null) {
              return ("MetaDataExportedType("+this.flags.ToString("x")+","+
                      this.typeDefId+","+this.typeNamespace+"."+
                      this.typeName+","+this.implementationIndex+")");
          }
          else {
              return ("MetaDataExportedType("+this.flags.ToString("x")+","+
                      this.typeDef+","+this.typeNamespace+"."+
                      this.typeName+","+this.implementation+")");
          }
      }

      // State

      private readonly int                    flags;
      private readonly int                    typeDefId;
      private          MetaDataTypeDefinition typeDef;
      private readonly String                 typeName;
      private readonly String                 typeNamespace;
      private readonly int                    implementationIndex;
      private          MetaDataObject         implementation;

  }

}

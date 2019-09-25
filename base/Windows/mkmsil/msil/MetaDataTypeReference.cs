// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataTypeReference: MetaDataObject {

      // Constructor Methods

      internal MetaDataTypeReference(int resolutionScopeIndex,
                                     String name, String nameSpace) {
          this.resolutionScopeIndex = resolutionScopeIndex;
          this.name = name;
          this.nameSpace = nameSpace;
      }

      // This is technically not a constructor method, but it is meant
      // to be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.resolutionScope =
              loader.getResolutionScope(this.resolutionScopeIndex);
      }

      // Access Methods

      // Returns one of MetaData{Module,ModuleRef,AssemblyRef,TypeReference}
      public MetaDataObject ResolutionScope {
          get {
              return this.resolutionScope;
          }
      }

      public String Name {
          get {
              return this.name;
          }
      }

      public String Namespace {
          get {
              return this.nameSpace;
          }
      }

      public string FullName {
          get {
              return ((this.Namespace.Length == 0) ?
                      this.Name :
                      this.Namespace + "." + this.Name);
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataTypeReference("+this.FullName+")");
      }

      public override String ToStringLong() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataTypeReference(");
          if (this.resolutionScope == null) {
              sb.Append(this.resolutionScopeIndex);
              sb.Append(",");
          }
          else {
              sb.Append("[");
              sb.Append(this.resolutionScope);
              sb.Append("]");
          }
          sb.Append(this.FullName);
          sb.Append(")");
          return sb.ToString();
      }

      // State

      private readonly int            resolutionScopeIndex;
      private          MetaDataObject resolutionScope;
      private readonly String         name;
      private readonly String         nameSpace;

  }

}

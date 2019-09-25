// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataDeclSecurity: MetaDataObject {

      // Constructor Methods

      internal MetaDataDeclSecurity(short action, int parentIndex,
                                    MetaDataBlob permissionSet) {
          this.action = action;
          this.parentIndex = parentIndex;
          this.permissionSet = permissionSet;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.parent = loader.getHasDeclSecurity(this.parentIndex);
      }

      // Access Methods

      public short Action {
          get {
              return this.action;
          }
      }

      public MetaDataObject Parent {
          get {
              return this.parent;
          }
      }

      public MetaDataBlob PermissionSet {
          get {
              return this.permissionSet;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (parent == null) {
              return ("MetaDataDeclSecurity("+this.action+","+this.parentIndex+
                      ","+this.permissionSet+")");
          }
          else {
              return ("MetaDataDeclSecurity("+this.action+","+this.parent+","+
                      this.permissionSet+")");
          }
      }

      // State

      private readonly short          action;
      private readonly int            parentIndex;
      private          MetaDataObject parent;
      private readonly MetaDataBlob   permissionSet;

  }

}

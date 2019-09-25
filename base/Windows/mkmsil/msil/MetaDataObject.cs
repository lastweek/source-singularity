// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.Collections;
using System.IO;

namespace Bartok.MSIL
{

  public abstract class MetaDataObject {

      // This class's primary reason for existence is its place in the
      // class hierarchy.

      // Convenient place to store CustomAttribute information

      public ArrayList CustomAttributes {
          get { return this.customAttributes; }
      }

      internal void AddCustomAttribute(MetaDataCustomAttribute ca) {
          if (this.customAttributes == null) {
              this.customAttributes = new ArrayList(2);
          }
          this.customAttributes.Add(ca);
      }

#region SyncBlockHack
      // Equality methods

      public override bool Equals(Object o) {
          return this == o;
      }

      public override int GetHashCode() {
          if (hash == 0) {
              if (nextHash == 0) {
                  nextHash++;
              }
              hash = nextHash++;
          }
          return hash;
      }
#endregion

      // Debug Methods

      public virtual String ToStringLong() {
          return this.ToString();
      }

      // Fields

      private ArrayList customAttributes;
#region SyncBlockHack
      private int hash;
      private static int nextHash;
#endregion
  }

}

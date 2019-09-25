// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;

  public class MetaDataMethodSpec: MetaDataObject {

      // Constructor Methods

      internal MetaDataMethodSpec(int methodIndex, byte[] data)
      {
          this.methodIndex = methodIndex;
          this.data = data;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.method = loader.getMethodDefOrRef(this.methodIndex);
      }

      // Access Methods

      // Method or MemberRef
      public MetaDataObject Method {
          get {
              return this.method;
          }
      }

      public byte[] Data {
          get {
              return this.data;
          }
      }

      // Debug Methods

      public override String ToString() {
          return "MetaDataMethodSpec()";
      }

      public override String ToStringLong() {
          return "MetaDataMethodSpec("+this.methodIndex+")";
      }

      // State

      private readonly int methodIndex;
      private          MetaDataObject method;
      private readonly byte[] data;
  }

}

// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataAssemblyOS: MetaDataObject {

      // Constructor Methods

      internal MetaDataAssemblyOS(int platformID, int majorVersion,
                                  int minorVersion) {
          this.platformID = platformID;
          this.majorVersion = majorVersion;
          this.minorVersion = minorVersion;
      }

      // Access Methods

      public int PlatformID {
          get {
              return this.platformID;
          }
      }

      public int MajorVersion {
          get {
              return this.majorVersion;
          }
      }

      public int MinorVersion {
          get {
              return this.minorVersion;
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataAssemblyOS("+this.platformID+","+
                  this.majorVersion+","+this.minorVersion+")");
      }

      // State

      private readonly int platformID;
      private readonly int majorVersion;
      private readonly int minorVersion;

  }

}

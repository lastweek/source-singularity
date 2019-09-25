// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataAssemblyRefOS: MetaDataObject {

      // Constructor Methods

      internal MetaDataAssemblyRefOS(int platformId, int majorVersion,
                                     int minorVersion,
                                     MetaDataAssemblyRef assemblyRef) {
          this.platformId = platformId;
          this.majorVersion = majorVersion;
          this.minorVersion = minorVersion;
          this.assemblyRef = assemblyRef;
      }

      // Access Methods

      public int PlatformID {
          get {
              return this.platformId;
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

      public MetaDataAssemblyRef AssemblyRef {
          get {
              return this.assemblyRef;
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataAssemblyRefOS("+this.platformId+","+
                  this.majorVersion+","+this.minorVersion+","+
                  this.assemblyRef+")");
      }

      // State

      private readonly int                 platformId;
      private readonly int                 majorVersion;
      private readonly int                 minorVersion;
      private readonly MetaDataAssemblyRef assemblyRef;

  }

}

// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataManifestResource: MetaDataObject {

      // Constructor Methods

      internal MetaDataManifestResource(int offset, int flags, String name,
                                        byte[] data, int implementationIndex)
      {
          this.offset = offset;
          this.flags = flags;
          this.name = name;
          this.data = data;
          this.implementationIndex = implementationIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.implementation =
              loader.getImplementation(this.implementationIndex);
      }

      // Access Methods

      public int Offset {
          get {
              return this.offset;
          }
      }

      // Bitmask described by ManifestResourceAttributes
      public int Flags {
          get {
              return this.flags;
          }
      }

      public String Name {
          get {
              return this.name;
          }
      }

      // Returns one of MetaData{File,AssemblyRef,ExportedType}
      public MetaDataObject Implementation {
          get {
              return this.implementation;
          }
      }

      public byte[] Data {
          get {
              return this.data;
          }
      }

      // Debug Methods

      public override String ToString() {
          return "MetaDataManifestResource("+this.name+")";
      }

      public override String ToStringLong() {
          if (this.implementation == null) {
              return ("MetaDataManifestResource("+this.offset+","+
                      this.flags.ToString("x")+","+this.name+","+
                      this.implementationIndex+")");
          }
          else {
              return ("MetaDataManifestResource("+this.offset+","+
                      this.flags.ToString("x")+","+this.name+","+
                      this.implementation+")");
          }
      }

      // State

      private readonly int offset;
      private readonly int flags;
      private readonly String name;
      private readonly byte[] data;
      private readonly int implementationIndex;
      private          MetaDataObject implementation;

      // Internal Classes

      // Section 22.1.6 of ECMA spec, Section II
      public enum ManifestResourceAttributes {
          VisibilityMask = 0x0007,
              Public     = 0x0001, // The Resource is exported from the Assembly.
              Private    = 0x0002  // The Resource is private to the Assembly.
      }

  }

}

//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataFile: MetaDataObject {

      // Constructor Methods

      internal MetaDataFile(int flags, String name, byte[] hashValue) {
          this.flags = flags;
          this.name = name;
          this.hashValue = hashValue;
      }

      // Access Methods

      // Bitmask described by FileAttributes
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

      public byte[] HashValue {
          get {
              return this.hashValue;
          }
      }

      // Debug Methods

      public override String ToString() {
          return "MetaDataFile("+this.name+")";
      }

      public override String ToStringLong() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataFile(");
          sb.Append(this.flags.ToString("x"));
          sb.Append(",");
          sb.Append(this.name);
          sb.Append(",[");
          int count = this.hashValue.Length;
          if (count > 0) {
              sb.Append("0x");
              sb.Append(this.hashValue[0].ToString("x2"));
              for (int i = 1; i < this.hashValue.Length; i++) {
                  sb.Append(",0x");
                  sb.Append(this.hashValue[i].ToString("x2"));
              }
          }
          sb.Append("])");
          return sb.ToString();
      }

      // State

      private readonly int    flags;
      private readonly String name;
      private readonly byte[] hashValue;

      // Internal Classes

      // Section 22.1.4 of ECMA spec, Section II
      public enum FileAttributes {
          ContainsMetaData       = 0x0000, // This is not a resource file,
              ContainsNoMetaData = 0x0001  // This is a resource file or other non-metadata-containing file
      }

  }

}

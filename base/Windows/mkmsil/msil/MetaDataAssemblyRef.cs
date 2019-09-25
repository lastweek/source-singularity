// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataAssemblyRef: MetaDataObject {

      // Constructor Methods

      internal MetaDataAssemblyRef(short majorVersion, short minorVersion,
                                   short buildNumber, short revisionNumber,
                                   int flags, byte[] publicKey,
                                   String name, String locale,
                                   byte[] hashValue) {
          this.majorVersion = majorVersion;
          this.minorVersion = minorVersion;
          this.buildNumber = buildNumber;
          this.revisionNumber = revisionNumber;
          this.flags = flags;
          this.publicKey = publicKey;
          this.name = name;
          this.locale = locale;
          this.hashValue = hashValue;
      }

      // Access Methods

      public short MajorVersion {
          get {
              return this.majorVersion;
          }
      }

      public short MinorVersion {
          get {
              return this.minorVersion;
          }
      }

      public short BuildNumber {
          get {
              return this.buildNumber;
          }
      }

      public short RevisionNumber {
          get {
              return this.revisionNumber;
          }
      }

      public int Flags {
          get {
              return this.flags;
          }
      }

      public byte[] PublicKey {
          get {
              return this.publicKey;
          }
      }

      public String Name {
          get {
              return this.name;
          }
      }

      public String Locale {
          get {
              return this.locale;
          }
      }

      public byte[] HashValue {
          get {
              return this.hashValue;
          }
      }

      // Debug Methods

      public override String ToString() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataAssemblyRef(");
          sb.Append(this.majorVersion);
          sb.Append(",");
          sb.Append(this.minorVersion);
          sb.Append(",");
          sb.Append(this.buildNumber);
          sb.Append(",");
          sb.Append(this.revisionNumber);
          sb.Append(",");
          sb.Append(this.flags.ToString("x"));
          sb.Append(",[");
          int count = this.publicKey.Length;
          if (count > 0) {
              sb.Append("0x");
              sb.Append(this.publicKey[0].ToString("x2"));
              for (int i = 1; i < count; i++) {
                  sb.Append(",0x");
                  sb.Append(this.publicKey[i].ToString("x2"));
              }
          }
          sb.Append("],");
          sb.Append(this.name);
          sb.Append(",");
          sb.Append(this.locale);
          sb.Append(",[");
          count = this.hashValue.Length;
          if (count > 0) {
              sb.Append("0x");
              sb.Append(this.hashValue[0].ToString("x2"));
              for (int i = 1; i < count; i++) {
                  sb.Append(",0x");
                  sb.Append(this.hashValue[i].ToString("x2"));
              }
          }
          sb.Append("])");
          return sb.ToString();
      }

      // State

      private readonly short  majorVersion;
      private readonly short  minorVersion;
      private readonly short  buildNumber;
      private readonly short  revisionNumber;
      private readonly int    flags;
      private readonly byte[] publicKey;
      private readonly String name;
      private readonly String locale;
      private readonly byte[] hashValue;

  }

}

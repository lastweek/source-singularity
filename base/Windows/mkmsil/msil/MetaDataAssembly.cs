//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataAssembly: MetaDataObject {

      // Constructor Methods

      internal MetaDataAssembly(int hashAlgorithmId,
                                short majorVersion, short minorVersion,
                                short buildNumber, short revisionNumber,
                                int flags, byte[] publicKey,
                                String name, String locale) {
          this.hashAlgorithmId = (AssemblyHashAlgorithmID) hashAlgorithmId;
          this.majorVersion = majorVersion;
          this.minorVersion = minorVersion;
          this.buildNumber = buildNumber;
          this.revisionNumber = revisionNumber;
          this.flags = flags;
          this.publicKey = publicKey;
          this.name = name;
          this.locale = locale;
      }

      // Access Methods

      public AssemblyHashAlgorithmID HashAlgorithmID {
          get {
              return this.hashAlgorithmId;
          }
      }

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

      // Bitmask described by AssemblyFlagsMask
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

      // Debug Methods

      public override String ToString() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataAssembly(");
          sb.Append(this.hashAlgorithmId);
          sb.Append(",");
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
          sb.Append(")");
          return sb.ToString();
      }

      // State

      private readonly AssemblyHashAlgorithmID hashAlgorithmId;
      private readonly short                   majorVersion;
      private readonly short                   minorVersion;
      private readonly short                   buildNumber;
      private readonly short                   revisionNumber;
      private readonly int                     flags;
      private readonly byte[]                  publicKey;
      private readonly String                  name;
      private readonly String                  locale;

      // Internal Classes

      // Section 22.1.1 of ECMA spec, section II
      public enum AssemblyHashAlgorithmID {
          None                     = 0x0000,
              MD5                  = 0x8003,
              SHA1                 = 0x8004
      }

      public enum AssemblyFlagMasks {
          PublicKey                      = 0x0001, // The assembly ref holds the full (unhashed) public key.
              CompatibilityMask          = 0x0070,
              SideBySideCompatible       = 0x0000, // The assembly is side by side compatible.
              NonSideBySideAppDomain     = 0x0010, // The assembly cannot execute with other versions if
                                                   // they are executing in the same application domain.
              NonSideBySideProcess       = 0x0020, // The assembly cannot execute with other versions if
                                                   // they are executing in the same process.
              NonSideBySideMachine       = 0x0030, // The assembly cannot execute with other versions if
                                                   // they are executing on the same machine.
              EnableJITcompileTracking   = 0x8000, // From "DebuggableAttribute".
              DisableJITcompileOptimizer = 0x4000  // From "DebuggableAttribute".
      }

  }

}

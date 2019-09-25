// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  // Information about unmanaged fields and methods that may
  // be called from managed code.
  public class MetaDataImplMap: MetaDataObject {

      // Constructor Methods

      internal MetaDataImplMap(short flags, int memberForwardedIndex,
                               String importName, int importScopeIndex) {
          this.flags = flags;
          this.memberForwardedIndex = memberForwardedIndex;
          this.importName = importName;
          this.importScopeIndex = importScopeIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.memberForwarded =
              loader.getMemberForwarded(this.memberForwardedIndex);
          this.importScope = loader.getModuleRef(this.importScopeIndex);
      }

      // Access Methods

      // Bitmask described by PInvokeAttributes
      public short Flags {
          get {
              return this.flags;
          }
      }

      // The metadata object that names the unmanaged field or method
      // Returns one of MetaData{Field,Method}
      public MetaDataObject MemberForwarded {
          get {
              return this.memberForwarded;
          }
      }

      public String ImportName {
          get {
              return this.importName;
          }
      }

      public MetaDataModuleRef ImportScope {
          get {
              return this.importScope;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.memberForwarded == null || this.importScope == null) {
              return ("MetaDataImplMap("+this.flags.ToString("x")+","+
                      this.memberForwardedIndex+","+this.importName+","+
                      this.importScopeIndex+")");
          }
          else {
              return ("MetaDataImplMap("+this.flags.ToString("x")+","+
                      this.memberForwarded+","+this.importName+","+
                      this.importScope+")");
          }
      }

      // State

      private readonly short             flags;
      private readonly int               memberForwardedIndex;
      private          MetaDataObject    memberForwarded;
      private readonly String            importName;
      private readonly int               importScopeIndex;
      private          MetaDataModuleRef importScope;

      // Internal Classes

      // Section 22.1.5 of ECMA spec, Section II
      public enum PInvokeAttributes {
          NoMangle              = 0x0001, // Pinvoke is to use the member name as specified.
              // Character set flags
              CharSetMask       = 0x0006, // Use this mask to retrieve the CharSet information.
              CharSetNotSpec    = 0x0000,
              CharSetAnsi       = 0x0002, 
              CharSetUnicode    = 0x0004,
              CharSetAuto       = 0x0006,
              SupportsLastError = 0x0040, // Information about target function. Not relevant for fields.
              // None of the calling convention flags is relevant for fields.
              CallConvMask      = 0x0700,
              CallConvWinapi    = 0x0100, // Pinvoke will use native callconv appropriate to target windows platform.
              CallConvCdecl     = 0x0200,
              CallConvStdcall   = 0x0300,
              CallConvThiscall  = 0x0400, // In M9, pinvoke will raise exception.
              CallConvFastcall  = 0x0500
      }

  }

}

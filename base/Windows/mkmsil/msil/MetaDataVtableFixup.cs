//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;

  // V-table constants from clr inc\corhdr.h
  [Flags]
  public enum COR_VTABLE : short {
      // V-table slots are 32-bits in size.
      _32BIT                          = 0x01,
      // V-table slots are 64-bits in size.
      _64BIT                          = 0x02,
      // If set, transition from unmanaged.
      FROM_UNMANAGED                  = 0x04,
      // If set, transition from unmanaged with keeping the current appdomain.
      FROM_UNMANAGED_RETAIN_APPDOMAIN = 0x08,
      // Call most derived method described by
      CALL_MOST_DERIVED               = 0x10
  }

  public class MetaDataVtableFixup: MetaDataObject {
      
      // Constructor Methods
      
      internal MetaDataVtableFixup(int rva, short size, COR_VTABLE type,
                                   MetaDataMethod[] fixupMethods) {
          this.rva = rva;
          this.size = size;
          this.type = type;
          this.fixupMethods = fixupMethods;
      }

      // Access Methods
      
      public int RVA {
          get { return this.rva; }
      }

      public short Size {
          get { return this.size; }
      }

      public COR_VTABLE Type {
          get { return this.type; }
      }

      public MetaDataMethod[] FixupMethods {
          get { return this.fixupMethods; }
      }

      private readonly int rva;
      private readonly short size;
      private readonly COR_VTABLE type;
      private readonly MetaDataMethod[] fixupMethods;
  }
}

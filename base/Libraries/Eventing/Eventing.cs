// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;

namespace Microsoft.Singularity.Eventing
{
  public class EventAttribute : Attribute
  {
      // mark classes & methods for eventing
  }

  public class EventEnumAttribute : Attribute
  {
      // mark classes & methods for eventing
  }

  // temporary class for data type - need to move this into DataType in core libs
  public class DataType2
  {
      public ushort __Boolean;
      public ushort __Int8;
      public ushort __UInt8;
      public ushort __Int16;
      public ushort __UInt16;
      public ushort __Int32;
      public ushort __UInt32;
      public ushort __Int64;
      public ushort __UInt64;
      public ushort __String;
      public ushort __EachParam; // hack! necessary for template to compile

      public DataType2()
      {
          __EachParam = 0;
          __Boolean = 1;
          __Int8 = 1;
          __UInt8 = 2;
          __Int16 = 3;
          __UInt16 = 4;
          __Int32 = 5;
          __UInt32 = 6;
          __Int64 = 7;
          __UInt64 = 8;

          __String = 0x4000; 
      }
  }
}



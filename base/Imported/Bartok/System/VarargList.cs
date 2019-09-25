//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace System
{

  using System.Runtime.CompilerServices;

  [RequiredByBartok]
  internal struct VarargList {
      internal int count;
      // TODO: inline vector of typed references will go here

      [RequiredByBartok]
      internal static VarargList Create(int count) {
          VarargList v;
          v.count = count;
          return v;
      }
  }
}

//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Audit;

namespace System.Runtime.CompilerServices {

  [AllCallees][NoAllocInstr]
  public sealed partial class NoHeapAllocationAttribute : Attribute {
  }

  [AllCallees] // must be recursive
  public sealed partial class NoBarriersAttribute: Attribute {
  }
}

namespace System.Runtime.InteropServices
{
    public enum GCOption {
        NONE = 0,
        GCFRIEND = 1,
        NOGC = 2,
        NOSTGC = 3,
    }

    [AttributeUsage(AttributeTargets.Method, Inherited = false)]
    [RequiredByBartok]
    public sealed class GCAnnotationAttribute : Attribute {
        internal GCOption _options;
        public GCAnnotationAttribute(GCOption options ) {
            _options = options;
        }
    }
}

  // special meta-attributes used to flag attributes which audit.exe looks at

namespace Microsoft.Singularity.Audit
{
  public class AllCalleesAttribute : Attribute
  {
      public AllCalleesAttribute() {}
  }
  public class NoAllocInstrAttribute : Attribute
  {
      public NoAllocInstrAttribute() {}
  }
  public class LayerAttribute : Attribute
  {
      public LayerAttribute(int n) {}
  }
}

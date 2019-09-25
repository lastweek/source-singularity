// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*============================================================
**
** File:    Version
**
** Purpose:
**
===========================================================*/
namespace System
{

    using System.Runtime.CompilerServices;

    // A Version object contains four hierarchical numeric components: major, minor,
    // build and revision.  Build and revision may be unspecified, which is represented
    // internally as a -1.  By definition, an unspecified component matches anything
    // (both unspecified and specified), and an unspecified component is "less than" any
    // specified component.

    //| <include path='docs/doc[@for="Version"]/*' />
    [RequiredByBartok]
    public sealed partial class Version : IComparable
    {
    }
}

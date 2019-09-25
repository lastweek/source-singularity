// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*============================================================
**
** File:    AssemblyName
**
** Purpose: Used for binding and retrieving info about an assembly
**
===========================================================*/
namespace System.Reflection
{
    using System.Runtime.CompilerServices;

    [RequiredByBartok]
    public partial class AssemblyName {
        [RequiredByBartok]
        private String _Culture;
        [RequiredByBartok]
        private String          _Name;                  // Name
        [RequiredByBartok]
        private byte[]          _PublicKeyToken;
        [RequiredByBartok]
        private Version         _Version;
    }
}

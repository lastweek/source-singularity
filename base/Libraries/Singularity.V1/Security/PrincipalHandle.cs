///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: PrincipalHandle.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.V1.Security
{
    public struct PrincipalHandle
    {
        public readonly long val;

        private const int DefaultPrincipalSize = 200;
        private const int DefaultAclIndirectSize = 512;

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern PrincipalHandle SelfPrincipalHandle();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        private static extern unsafe int GetPrincipalNameImpl(PrincipalHandle handle,
                                                  /*[out]*/ char *outName, int outNameLength);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        private static extern unsafe int ExpandAclIndirectionImpl(
                                                  /*[in]*/ char *name, int nameLength,
                                                  /*[out]*/ char *outText, int outTextLength);

        public static unsafe string GetPrincipalName(PrincipalHandle handle)
        {
            int size = DefaultPrincipalSize;
            for (;;) {
                char[] name = new char[size];
                fixed (char *namePtr = &name[0]) {
                    int len = GetPrincipalNameImpl(handle, namePtr, size);
                    if (len >= 0)
                        return String.StringCTOR(name, 0, len);
                    size = -len;
                }
            }
        }

        public static unsafe string ExpandAclIndirection(string name)
        {
            if (name == null)
                return null;

            int size = DefaultAclIndirectSize;
            // convert string to char* and length
            char [] strChar = new char[name.Length];
            name.CopyTo(0, strChar, 0, name.Length);
            fixed (char *inname = &strChar[0]) {
                for (;;) {
                    char[] result = new char[size];
                    fixed (char *resultPtr = &result[0]) {
                        int len = ExpandAclIndirectionImpl(inname, name.Length, resultPtr, size);
                        if (len == 0)
                            return null;
                        if (len > 0)
                            return String.StringCTOR(result, 0, len);
                        size = -len;
                    }
                }
            }
        }
    }
}

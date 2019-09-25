///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: PrincipalId.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity.Security;

namespace Microsoft.Singularity.V1.Security
{
    [CLSCompliant(false)]
    public struct PrincipalHandle
    {
        public readonly ulong val;

        internal PrincipalHandle(ulong val)
        {
            this.val = val;
        }

        [ExternalEntryPoint]
        public static PrincipalHandle SelfPrincipalHandle()
        {
            return new PrincipalHandle(Thread.CurrentProcess.Principal.Val);
        }

        // For the following routine, assume that the length of the output string
        // is nchars.  If nchars is larger than outNameLength, this routine returns
        // -nchars without touching outName.  Otherwise, the output string is copied
        // into outName, and nchars is returns.   
        [ExternalEntryPoint]
        public static unsafe int GetPrincipalNameImpl(PrincipalHandle handle,
                                                  /*[out]*/ char *outName, int outNameLength)
        {
            Principal p = PrincipalImpl.MakePrincipal(handle.val);
            string name = p.GetName();
            if (name.Length > outNameLength)
                return (-name.Length);
            return name.InternalGetChars(outName, outNameLength);
        }

        [ExternalEntryPoint]
        public static unsafe int ExpandAclIndirectionImpl(/*[in]*/ char *name, int nameLength,
                                                  /*[out]*/ char *outText, int outTextLength)
        {
            if (name == null || nameLength == 0)
                return 0;

            string myname = String.StringCTOR(name, 0, nameLength);
            string res = PrincipalImpl.ExpandAclIndirection(myname);
            if (res == null || res.Length == 0)
                return 0;
            if (res.Length > outTextLength)
                return (-res.Length);
            return res.InternalGetChars(outText, outTextLength);
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: SystemType.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity.V1.Types
{
    public struct SystemType
    {
        /// A handle to a RuntimeSystemType
        private readonly UIntPtr id;

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(320)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern SystemType RootSystemType();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1472)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        unsafe public static extern SystemType Register(char* name,
                                                        int nameLength,
                                                        long lowerHash,
                                                        long upperHash,
                                                        SystemType parent);


        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool IsSubtype(SystemType child,
                                            SystemType parent);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        unsafe public static extern bool IsSubtype(SharedHeapService.Allocation* childData,
                                                   SystemType parent);

        [NoHeapAllocation]
        public static bool IsNull(SystemType st)
        {
            return st.id == UIntPtr.Zero;
        }

        [CLSCompliant(false)]
        public UIntPtr TypeId
        {
            [NoHeapAllocation]
            get {
                return this.id;
            }
        }
    }
}

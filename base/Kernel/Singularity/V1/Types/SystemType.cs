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
using System.Threading;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity.V1.Types
{
    public struct SystemType
    {
        /// A handle to a RuntimeSystemType
        internal readonly UIntPtr id;

        internal SystemType(UIntPtr typeHandle) {
            this.id = typeHandle;
        }

        [ExternalEntryPoint]
        public static SystemType RootSystemType()
        {
            UIntPtr rootRuntimeSystemTypeHandle = RuntimeSystemType.GetRootHandle();

            return new SystemType(rootRuntimeSystemTypeHandle);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        unsafe public static SystemType Register(char* name,
                                                 int   nameLength,
                                                 long  lowerHash,
                                                 long  upperHash,
                                                 SystemType parent)
        {
            string sname = new String(name, 0, nameLength);
            return Register(sname, lowerHash, upperHash, parent);
        }

        /// Called from Binder which lives in a separate dll.
        public static SystemType Register(string name,
                                          long lowerHash,
                                          long upperHash,
                                          SystemType parent)
        {
            RuntimeSystemType parentrts = HandleTable.GetHandle(parent.id) as RuntimeSystemType;

#if false
            DebugStub.WriteLine("SystemType.Register '{0}' hash0={1:x8} hash1={2:x8} Parent {3}",
                                __arglist(name, lowerHash, upperHash, parent.TypeId));

            Tracing.Log(Tracing.Debug, "Type '{0}' (parent={1:x8})",
                        name, parent.id);
            Tracing.Log(Tracing.Debug, "hash0={0:x8} hash1={1:x8}",
                        lowerHash.ToString(), upperHash.ToString());
#endif // false

            UIntPtr childHandle = parentrts.LookupChildHandle(name, lowerHash, upperHash);

#if false
            Tracing.Log(Tracing.Debug, "result UIntPtr = {0:x8}", childHandle);
#endif // false

            SystemType ret = new SystemType(childHandle);
            return ret;
        }

        [ExternalEntryPoint]
        public static bool IsSubtype(SystemType child,
                                     SystemType parent)
        {
            return IsSubtype(child.id, parent.id);
        }

        private static bool IsSubtype(UIntPtr childHandle, UIntPtr parentHandle)
        {
            if (childHandle == UIntPtr.Zero) {
                return false;
            }
            if (parentHandle == UIntPtr.Zero) return false;

            RuntimeSystemType childrts = HandleTable.GetHandle(childHandle) as RuntimeSystemType;

            if(childrts == null) {
                DebugStub.Print("Ack! Runtime: IsSubType is null!\n");
                return false;
            }

            bool ret = childrts.IsSubtype(parentHandle);

            if (ret) {
#if false
                Tracing.Log(Tracing.Debug,
                            "SystemType.IsSubtype(parent={0:x8}, child={1:x8}) = [true]",
                            parentHandle, childHandle);

                DebugStub.WriteLine("SystemType.IsSubtype(parent={0:x8}, child={1:x8}) = [true]",
                                    __arglist(parentHandle, childHandle)
                                    );
#endif
            }
            else {
#if false
                Tracing.Log(Tracing.Debug,
                            "SystemType.IsSubtype(parent={0:x8}, child={1:x8}) = [false]",
                            parentHandle, childHandle);

                DebugStub.WriteLine("SystemType.IsSubtype(parent={0:x8}, child={1:x8}) = [false]",
                                    __arglist(parentHandle, childHandle)
                                    );
#endif
            }
            return ret;
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        unsafe public static bool IsSubtype(SharedHeapService.Allocation* childData,
                                            SystemType parent)
        {
            UIntPtr childHandle = SharedHeapService.GetType(childData);
            return IsSubtype(childHandle, parent.id);
        }

        [CLSCompliant(false)]
        unsafe public static bool IsSubtype(SharedHeap.Allocation* childData,
                                            SystemType parent)
        {
            UIntPtr childHandle = SharedHeap.Allocation.GetType(childData);
            return IsSubtype(childHandle, parent.id);
        }

        public static bool IsNull(SystemType st) { return st.id == UIntPtr.Zero; }

        [CLSCompliant(false)]
        public UIntPtr TypeId { get { return this.id; } }
    }
}

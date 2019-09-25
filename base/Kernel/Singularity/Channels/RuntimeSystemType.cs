////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   RuntimeSystemType.cs
//
//  Note: Represents system wide types. They live in the Kernel GC heap and are
//        mapped to via handles from type Singularity.V1.SystemType
//
using System;
using System.Collections;
using System.Diagnostics;
using Microsoft.Singularity;
using Microsoft.Singularity.Memory;

namespace Microsoft.Singularity.Channels
{

    public class RuntimeSystemType {

        private struct MD5TypeEntry : IComparable
        {
            public readonly string name;
            public readonly long lowerHash;
            public readonly long upperHash;

            public MD5TypeEntry(string name) : this(name, 0, 0) {}

            public MD5TypeEntry(string name, long lower, long upper) {
                this.name = name;
                this.lowerHash = lower;
                this.upperHash = upper;
            }

            int IComparable.CompareTo(object o2)
            {
                MD5TypeEntry m2 = (MD5TypeEntry)o2;

                if (upperHash < m2.upperHash) {
                    return -1;
                }
                else if (upperHash > m2.upperHash) {
                    return 1;
                }
                else if (lowerHash < m2.lowerHash) {
                    return -1;
                }
                else if (lowerHash > m2.lowerHash) {
                    return 1;
                }
                return this.name.CompareTo(m2.name);

#if false
                long d1 = unchecked(this.upperHash - m2.upperHash);

                if (d1 == 0) {
                    long d2 = unchecked(this.lowerHash - m2.lowerHash);
                    if (d2 == 0) return 0;
                    if (d2 < 0) return -1;
                    return +1;
                }
                if (d1 < 0) return -1;
                return +1;
#endif

            }
        }

        private MD5TypeEntry hash;
        private RuntimeSystemType parent;
        private UIntPtr handle;

        [Conditional("DEBUG_RUNTIME_SYSTEM_TYPE_TREE")]
        [CLSCompliant(false)]
        public static void DebugLine(String format, __arglist)
        {
            DebugStub.WriteLine(format, new ArgIterator(__arglist));
        }

        private RuntimeSystemType(RuntimeSystemType parent, MD5TypeEntry hash)
        {
            this.hash = hash;
            this.parent = parent;
        }

        private static UIntPtr RootHandle;

        static RuntimeSystemType()
        {
            RootHandle = RuntimeSystemType.For(null, new MD5TypeEntry("System.Object"));
        }

        private static UIntPtr For(RuntimeSystemType parent, MD5TypeEntry hash)
        {
            RuntimeSystemType rts = new RuntimeSystemType(parent, hash);

            // IMPORTANT we need to allocate these handles to the kernel, since
            // they are stored in shared heap object headers that move from process
            // to process.
            rts.handle = Process.kernelProcess.AllocateHandle(rts);

            // TODO: Figure out how to collect them
            //
            return rts.handle;
        }


        public long Hash0 { get { return this.hash.lowerHash; } }
        public long Hash1 { get { return this.hash.upperHash; } }

        internal static UIntPtr GetRootHandle()
        {
            return RootHandle;
        }

        private SortedList ChildHandles = new SortedList();

        internal UIntPtr LookupChildHandle(string name, long lowerHash, long upperHash)
        {
            MD5TypeEntry childhash = new MD5TypeEntry(name, lowerHash, upperHash);

            object childBox = this.ChildHandles[childhash];
            if (childBox == null) {
                lock (this.ChildHandles) {
                    childBox = this.ChildHandles[childhash];
                    if (childBox == null) {
                        UIntPtr child = RuntimeSystemType.For(this, childhash);
                        this.ChildHandles.Add(childhash, child);
                        DebugLine("RST.LookupChild({0}.{1:x16}{2:x16}) => Create {3:x8}",
                                  __arglist(name, lowerHash, upperHash, child));
                        return child;
                    }
                }
            }
            DebugLine("RST.LookupChild({0}.{1:x16}{2:x16}) => Find {3:x8}",
                      __arglist(name, lowerHash, upperHash, (UIntPtr)childBox));
            return (UIntPtr)childBox;
        }

        internal bool IsSubtype(UIntPtr candidateHandle)
        {
            if (candidateHandle == UIntPtr.Zero) {
                DebugLine("RST.IsSubType {0:x8} of {1:x8} => false",
                          __arglist(candidateHandle, handle));
                return false;
            }

            RuntimeSystemType candidate = HandleTable.GetHandle(candidateHandle) as RuntimeSystemType;
            if (candidate == null) {
                DebugLine("RST.IsSubType {0:x8} of {1:x8} => false",
                          __arglist(candidateHandle, handle));
                return false;
            }

            RuntimeSystemType current = this;
            while (current != null) {
                if (current == candidate) {
                    DebugLine("RST.IsSubType {0:x8} of {1:x8} => true",
                              __arglist(candidateHandle, handle));
                    return true;
                }
                current = current.parent;
            }
            DebugLine("RST.IsSubType {0:x8} of {1:x8} => false",
                      __arglist(candidateHandle, handle));
            return false;
        }
    }
}

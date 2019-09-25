// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
// Simple PE Loader for Singularity
//
// Currently does not support:
//      x64
//      sections loaded at separate addresses
//      loading at preferred address

// #define verbose

namespace Microsoft.Singularity.Loader
{
    using Microsoft.Singularity;
    using Microsoft.Singularity.Io;

    using System;
    using System.Diagnostics;
    using System.Runtime.InteropServices;
    using System.Threading;

    [CLSCompliant(false)]
    internal class ExportTable
    {
        private IoMemory mem;
        private DirectoryEntry entry;
        private ExportDirectory exports;
        private string[] names;
        private ushort[] ordinals;
        private UIntPtr[] addresses;

        struct ExportDirectory
        {
            internal readonly uint   Characteristics;
            internal readonly uint   NumberOfFunctions;
            internal readonly uint   NumberOfNames;
            internal readonly uint   AddressOfFunctions;    // RVA from base of image
            internal readonly uint   AddressOfNames;        // RVA from base of image
            internal readonly uint   AddressOfOrdinals;     // RVA from base of image

            internal ExportDirectory(IoMemory mem, int offset)
            {
                if (offset + 40 > mem.Length) {
                    Error.AccessOutOfRange();
                }
                Characteristics     = mem.Read32Unchecked(offset + 0);
                NumberOfFunctions   = mem.Read32Unchecked(offset + 20);
                NumberOfNames       = mem.Read32Unchecked(offset + 24);
                AddressOfFunctions  = mem.Read32Unchecked(offset + 28);
                AddressOfNames      = mem.Read32Unchecked(offset + 32);
                AddressOfOrdinals   = mem.Read32Unchecked(offset + 36);

                if (AddressOfFunctions + 4 * NumberOfFunctions > mem.Length ||
                    AddressOfOrdinals + 2 * NumberOfFunctions > mem.Length ||
                    AddressOfNames + 4 * NumberOfFunctions > mem.Length) {

                    Error.AccessOutOfRange();
                }
            }
        }

        internal ExportTable(IoMemory mem, UIntPtr imageBase, DirectoryEntry entry)
        {
            this.mem = mem;
            this.entry = entry;

            try {
                exports = new ExportDirectory(mem, (int)entry.virtualAddress);

                if (exports.NumberOfFunctions > 0) {
                    addresses = new UIntPtr[exports.NumberOfFunctions];
                    for (uint i = 0; i < exports.NumberOfFunctions; i++) {
                        addresses[i] = imageBase
                            + mem.Read32Unchecked((int)(exports.AddressOfFunctions + 4 * i));
                    }
                }

                if (exports.NumberOfNames > 0) {
                    names = new string[exports.NumberOfNames];
                    ordinals = new ushort[exports.NumberOfNames];
                    for (uint i = 0; i < exports.NumberOfNames; i++) {
                        ordinals[i]
                            = mem.Read16Unchecked((int)(exports.AddressOfOrdinals + 2 * i));
                        uint addrOfName
                            = mem.Read32Unchecked((int)(exports.AddressOfNames + 4 * i));
                        names[i] = mem.ReadAsciiZeroString((int)addrOfName);
                    }
                }
            }
            catch (Exception e) {
                DebugStub.Print("Caught exception: {0}\n",
                                __arglist(e.ToString()));
            }
        }

        [Conditional("DEBUG")]
        internal void Dump()
        {
            DebugStub.Print("  Ord# Function Name\n");
            if (names != null) {
                for (int i = 0; i < names.Length; i++) {
                    DebugStub.Print("  {0:d4} {1:x8} {2:x8}\n",
                                    __arglist(ordinals[i], addresses[i], names[i]));
                }
            }
        }

        internal UIntPtr Resolve(ushort hint, string name)
        {
            if (names != null) {
                // we need to put a guard here.  because
                // hint might exceed names.Length The guard in
                // particular is useful when we want to resolve
                // imports from MP applications with abi.dll
                // (MpSyscalls.x86). The "hint" that is obtained from the
                // app.x86 is actually the hint related to kernel.x86.
                // Hence, when resolving imports for MP apps, we should
                // always fall through to the "else" block below
                if (hint < names.Length && names[hint] == name) {
                    return addresses[hint];
                }
                else {
                    // TODO: we should probably do a binary search.
                    for (int i = 0; i < names.Length; i++) {
                        if (names[i] == name) {
                            return addresses[i];
                        }
                    }
                }
            }
            return UIntPtr.Zero;
        }
    }
}

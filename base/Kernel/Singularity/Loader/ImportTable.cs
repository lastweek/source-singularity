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
    internal class ImportTable
    {
        private IoMemory mem;
        private DirectoryEntry entry;

        internal ImportTable(IoMemory mem, DirectoryEntry entry)
        {
            this.mem = mem;
            this.entry = entry;

            if (entry.size == 0) {
                DebugStub.WriteLine("// No import table.");
                return;
            }
        }

#if verbose
        [Conditional("DEBUG")]
        public void DumpIAT(String title)
        {
            Tracing.Log(Tracing.Debug, "// {0}", title);
            if (entry.size == 0) {
                Tracing.Log(Tracing.Debug, "// No data.");
                return;
            }
            int importOffset = (int)entry.virtualAddress;
            Tracing.Log(Tracing.Debug, "  import offset={0:x8}", importOffset);
            //
            // start at the importOffset specified above creating and filling out ImportDescriptors
            // There is no indication in the header as to how many descriptors are present.
            // In the last descriptor all fields will be 0; this code checks just the firstChunk field.
            //
            for (;;) {
                ImportDescriptor importDescriptor =
                    new ImportDescriptor(mem, ref importOffset);

                //Use hit/Name array pointed to by "characteristics"
                // FirstChunk points to the IAT table which is modified at load time to
                //  to reflect the fixed-up thunk to access the function
                if (importDescriptor.characteristics == 0) {
                    return;
                }
                String name = null;
                if (importDescriptor.name != 0) {
                    name = mem.ReadAsciiZeroString((int)importDescriptor.name);
                }
                Tracing.Log(Tracing.Debug, "// {0}", name);
                importDescriptor.DumpToStream();
                Tracing.Log(Tracing.Debug, "//");

                int importTableOffset = (int)importDescriptor.characteristics;
                for (;;) {
                    int importTableID = (int) mem.Read32(importTableOffset);
                    if (importTableID == 0) {
                        break;
                    }
                    Tracing.Log(Tracing.Debug, "importTableID is {0:x8}", importTableID);
                    int nameStringOffset =
                        importTableID & 0x7fffffff;
                    importTableOffset += 4;
                    if ((importTableID & 0x8000000) != 0) {
                        Tracing.Log(Tracing.Debug, "//              {0:x8} by ordinal {1:x8}",
                                    mem.Read16(importTableOffset),
                                    (importTableID & 0x7ffffff));
                    }
                    else {
                        Tracing.Log(Tracing.Debug, "//              {1:x8} {0:x8}",
                                    mem.ReadAsciiZeroString(nameStringOffset+2),
                                    mem.Read16(importTableOffset));
                    }
                }
                Tracing.Log(Tracing.Debug, "");
            }
            //throw new BadImageFormatException("");
        }
#endif

        public void ResolveImports(ExportTable exports)
        {
            if (entry.size == 0) {
                Tracing.Log(Tracing.Debug, "// No imports to resolve.");
                return;
            }

            int importOffset = (int)entry.virtualAddress;
            //Tracing.Log(Tracing.Debug, "  import offset={0:x8}", importOffset);
            //
            // start at the importOffset specified above creating and filling out ImportDescriptors
            // There is no indication in the header as to how many descriptors are present.
            // In the last descriptor all fields will be 0; this code checks just the firstChunk field.
            //
            for (;;) {
                ImportDescriptor importDescriptor =
                    new ImportDescriptor(mem, ref importOffset);
                if (importDescriptor.firstChunk == 0) {
                    return;
                }
                ushort hint = 0;
                String name = null;
                if (importDescriptor.name != 0) {
                    name = mem.ReadAsciiZeroString((int)importDescriptor.name);
                }

#if verbose
                Tracing.Log(Tracing.Debug, "//     {0}", name);
                importDescriptor.DumpToStream("//              ");
                Tracing.Log(Tracing.Debug, "//");
#endif
                UIntPtr offsetHintTable = UIntPtr.Zero;

                if (0 == importDescriptor.characteristics) {
                    offsetHintTable = (UIntPtr)importDescriptor.characteristics;
                }
                else {
                    offsetHintTable = (UIntPtr)importDescriptor.firstChunk;
                }
                UIntPtr offsetIAT = (UIntPtr)importDescriptor.firstChunk;

#if PTR_SIZE_64

                //
                // AIFIX: Add hint logic.
                //

                for (;;) {

                    ulong ImportEntry = (ulong) mem.Read64((int) offsetIAT);

                    if (ImportEntry == 0) {

                        break;
                    }

                    if ((ImportEntry >> 63) != 0) {

                        throw new BadImageFormatException("Import Ordinal encountered");
                    }

                    name = mem.ReadAsciiZeroString(((int) (ImportEntry & 0x7FFFFFFF)) + 2);

                    UIntPtr Address;

                    Address = exports.Resolve(hint, name);

                    if (Address == 0) {

                        throw new BadImageFormatException("Import not found");
                    }

                    mem.Write64((int) offsetIAT, (ulong) Address);

                    offsetIAT += 8;
                }

#else

                for (;;) {
                    // read elements in the hint array for processing
                    // the hint array terminates when the its content is 0
                    int importByNameEntry = (int) mem.Read32((int)offsetHintTable);
                    if (importByNameEntry == 0) break;
#if verbose
                    Tracing.Log(Tracing.Debug, "importByName entry is {0:x8}",
                                importByNameEntry);
#endif
                    int nameStringOffset = importByNameEntry & 0x7fffffff;
                    if ((importByNameEntry & 0x8000000) != 0) {
                        // should never happen in Singularity (no Ordinals)
                        throw new BadImageFormatException("Import Ordinal encountered");
                    }
                    else {
                        name = mem.ReadAsciiZeroString((int)nameStringOffset+2);
                        hint = mem.Read16Unchecked(nameStringOffset);
                        //Tracing.Log(Tracing.Debug, " function to lookup is {0}", name);

                        UIntPtr addr = exports.Resolve(hint, name);
                        if (0 != addr) {
                            //Overwrite ptr in IAT with address of function in the
                            // IAT thunk table
#if verbose
                            int meth = name.IndexOf('@');
                            int rest = name.IndexOf('@', meth + 1) + 1;
                            int clas = name.LastIndexOf('_', rest, rest - meth) + 1;
                            Tracing.Log(Tracing.Debug, "    import: {1:x8} is {2:x8} {0}",
                                        name.Substring(0, meth) + "@" + name.Substring(clas, rest - clas) + "@" name.Substring(rest)
                                        (uint)offsetIAT, (uint)addr);
#endif
                            mem.Write32((int) offsetIAT,(uint)addr);
                        }
                        else {
                            Tracing.Log(Tracing.Debug, " Import not found: {0}", name);
                            throw new BadImageFormatException("Import not found");
                        }
                    }
                    // increment "array indices"
                    offsetIAT += 4;
                    offsetHintTable +=4;
                }
                //Tracing.Log(Tracing.Debug, "");

#endif

            }
            //throw new BadImageFormatException("");
        }

        internal struct ImportDescriptor
        {
            internal ImportDescriptor(IoMemory mem, ref int offset)
            {
                if (offset + 20 > mem.Length) {
                    Error.AccessOutOfRange();
                }
                this.characteristics    = mem.Read32Unchecked(offset + 0);
                this.timeDateStamp      = mem.Read32Unchecked(offset + 4);
                this.forwarderChain     = mem.Read32Unchecked(offset + 8);
                this.name               = mem.Read32Unchecked(offset + 12);
                this.firstChunk         = mem.Read32Unchecked(offset + 16);
                offset += 20;
            }

            [Conditional("DEBUG")]
            internal void DumpToStream()
            {
                Tracing.Log(Tracing.Debug, "{0:x8}  Import Address Table", firstChunk);
                Tracing.Log(Tracing.Debug, "{0:x8}  Import Name Table", name);
                Tracing.Log(Tracing.Debug, "{0:x8}  Time date stamp", timeDateStamp);
                Tracing.Log(Tracing.Debug, "{0:x8}  Index of first forwarder reference",
                            forwarderChain);
            }

            // State

            internal readonly uint characteristics;
            internal readonly uint timeDateStamp;
            internal readonly uint forwarderChain;
            internal readonly uint name;
            internal readonly uint firstChunk;
        }
    } // ImportTable class
}

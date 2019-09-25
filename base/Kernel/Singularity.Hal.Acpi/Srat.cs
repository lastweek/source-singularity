///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    System Resource Affinity Table (SRAT)
//    Page 123 of ACPI 3.0 Spec.
//    Also see: "Static Resource Affinity Table" at www.microsoft.com

namespace Microsoft.Singularity.Hal.Acpi
{

    using System;
    using Microsoft.Singularity.Io;

    public class Srat
    {
        public const string Signature = "SRAT";
        private const int ProcessorStructureId = 0;
        private const int MemoryStructureId = 1;

        private int [] processorOffsets;
        private int [] memoryOffsets;

        private IoMemory          region;
        private SystemTableHeader header;


        public int GetNumberOfProcessors()
        {
            return processorOffsets.Length;
        }

        public int GetNumberOfMemories()
        {
            return memoryOffsets.Length;
        }

        // Processor fields offsets (important fields marked with XX)
        // -----------------------------------------------------------
        //     Entry                offsets      byte length
        // -----------------------------------------------------------
        //     Type               :   0
        //     Length             :   1
        //     Proximity Domain L :   2    XX
        //     APIC ID            :   3    XX
        //     Flags              :   4    XX
        //     Local SAPIC EID    :   8
        //     Proximity Domain H :   9
        //     Reserved           :  12
        public uint GetProcessorDomain(int processorIndex)
        {
            int offset = processorOffsets[processorIndex];
            uint domain = 0;
            domain = domain + region.Read8(offset+9) << 24;
            domain = domain + region.Read8(offset+10) << 16;
            domain = domain + region.Read8(offset+11) << 8;
            domain = domain + region.Read8(offset+2);
            return domain;
        }

        public uint GetProcessorApicId(int processorIndex)
        {
            return region.Read8(processorOffsets[processorIndex]+3);
        }

        public uint GetProcessorFlagIgnore(int processorIndex)
        {
            uint flags = region.Read32(processorOffsets[processorIndex]+4);
            return (flags & 0x1);
        }

        // Memory fields offsets (important fields marked with XX)
        // -----------------------------------------------------------
        //     Entry                offsets      byte length
        // -----------------------------------------------------------
        //     Type               :   0
        //     Length             :   1
        //     Proximity Domain   :   2    XX
        //     Reserved           :   6
        //     Base Address Low   :   8    XX
        //     Base Address High  :  12    XX
        //     Length Low         :  16    XX
        //     Length High        :  20    XX
        //     Reserved           :  24
        //     Flags              :  28    XX
        //     Reserved           :  32
        public uint GetMemoryDomain(int memoryIndex)
        {
            return (region.Read32(memoryOffsets[memoryIndex]+2));
        }

        public ulong GetMemoryBaseAddress(int memoryIndex)
        {
            int offset = memoryOffsets[memoryIndex];
            uint baseHigh = region.Read32(offset+12);
            uint baseLow  = region.Read32(offset+8);
            ulong baseAddr = (((ulong)baseHigh) << 32) + baseLow;
            return baseAddr;
        }

        public ulong GetMemoryEndAddress(int memoryIndex)
        {
            ulong baseAddr = GetMemoryBaseAddress(memoryIndex);
            ulong memSize = GetMemorySize(memoryIndex);
            return baseAddr+memSize;
        }

        public ulong GetMemorySize(int memoryIndex)
        {
            int offset = memoryOffsets[memoryIndex];
            uint lenHigh = region.Read32(offset+20);
            uint lenLow  = region.Read32(offset+16);
            ulong memSize = (((ulong)lenHigh) << 32) + lenLow;
            return memSize;
        }

        public uint GetMemoryFlagIgnore(int memoryIndex)
        {
            uint flags = region.Read32(memoryOffsets[memoryIndex]+28);
            return (flags & 0x1);
        }

        public uint GetMemoryFlagHotPluggable(int memoryIndex)
        {
            uint flags = region.Read32(memoryOffsets[memoryIndex]+28);
            return (flags & 0x2);
        }

        public uint GetMemoryFlagNonVolatile(int memoryIndex)
        {
            uint flags = region.Read32(memoryOffsets[memoryIndex]+28);
            return (flags & 0x4);
        }

        public Srat(IoMemory region, SystemTableHeader header)
        {
            this.region = region;
            this.header = header;
        }

        // Create() Srat
        public static Srat Create(SystemTableHeader header)
        {
            return new Srat(
                IoMemory.MapPhysicalMemory(
                    header.PostHeaderAddress, header.PostHeaderLength,
                    true, false
                    ),
                header
                );
        }

        // Parse Srat structure
        public void ParseSratStructure()
        {
            int offset = 12; // there are 12 bytes offset
            int processorCount = 0;
            int memoryCount = 0;
            int type,length;

            // 1st stage, count the number of processors
            // reset counter
            while (offset < region.Length) {

                type = region.Read8(offset);

                // this is a processor structure
                if (type == ProcessorStructureId) {
                    length = region.Read8(offset+1);
                    processorCount++;
                    offset += length;
                }
                // this is a memory structure
                else if (type == MemoryStructureId) {
                    length = region.Read8(offset+1);
                    memoryCount++;
                    offset += length;
                }
                else {
                    DebugStub.Print("  ERROR: Impossible Srat Id\n");
                    DebugStub.Break();
                    break;
                }
            }

            // 2nd stage, create arrays
            processorOffsets = new int [processorCount];
            memoryOffsets = new int [memoryCount];

            // 3rd stage: fill the offsets
            // clear everything first
            offset = 12;
            processorCount = 0;
            memoryCount = 0;

            while (offset < region.Length) {

                type = region.Read8(offset);

                // this is a processor structure
                if (type == ProcessorStructureId) {
                    length = region.Read8(offset+1);
                    processorOffsets[processorCount] = offset;
                    processorCount++;
                    offset += length;
                }
                // this is a memory structure
                else if (type == MemoryStructureId) {
                    length = region.Read8(offset+1);
                    memoryOffsets[memoryCount] = offset;
                    memoryCount++;
                    offset += length;
                }
                else {
                    DebugStub.Print("  ERROR: Impossible Srat Id\n");
                    DebugStub.Break();
                    break;
                }
            }
        }

        // Dump Srat structure
        public void DumpSratOffsets()
        {
            DebugStub.Print("\n\n\n  SRAT Offset Details: \n");
            DebugStub.Print("------------------------------------\n");
            DebugStub.Print("  {0} processors, {1} memories \n",
                            __arglist(processorOffsets.Length,
                                      memoryOffsets.Length));

            DebugStub.Print("  P Offset --  ");
            for (int i = 0; i < processorOffsets.Length; i++) {
                DebugStub.Print("{0}  ", __arglist(processorOffsets[i]));
            }
            DebugStub.Print("\n");
            DebugStub.Print("  M Offset --  ");
            for (int i = 0; i < memoryOffsets.Length; i++) {
                DebugStub.Print("{0}  ", __arglist(memoryOffsets[i]));
            }
            DebugStub.Print("\n\n\n");
        }

        // Dump Srat Important fields
        public void DumpSratImportantFields()
        {
            DebugStub.Print("\n\n\n  SRAT Important Fields: \n");
            DebugStub.Print("------------------------------------\n");


            for (int i = 0; i < processorOffsets.Length; i++) {
                DebugStub.Print("     PROCESSOR {0}\n",
                                __arglist(i));
                DebugStub.Print("         Domain  : {0}\n",
                                __arglist(GetProcessorDomain(i)));
                DebugStub.Print("         APIC ID : {0}\n",
                                __arglist(GetProcessorApicId(i)));
                DebugStub.Print("         Ignore  : {0}\n",
                                __arglist(GetProcessorFlagIgnore(i)));
            }

            for (int i = 0; i < memoryOffsets.Length; i++) {
                DebugStub.Print("     MEMORY {0}\n",
                                __arglist(i));
                DebugStub.Print("         Domain  : {0}\n",
                                __arglist(GetMemoryDomain(i)));
                DebugStub.Print("         Base    : {0} KB\n",
                                __arglist(GetMemoryBaseAddress(i)/1024));
                DebugStub.Print("         End     : {0} KB\n",
                                __arglist(GetMemoryEndAddress(i)/1024));
                DebugStub.Print("         MemSize : {0} KB\n",
                                __arglist(GetMemorySize(i)/1024));
                DebugStub.Print("         Ignore  : {0}\n",
                                __arglist(GetMemoryFlagIgnore(i)));
                DebugStub.Print("         HotPlug : {0}\n",
                                __arglist(GetMemoryFlagHotPluggable(i)));
                DebugStub.Print("         NonVol  : {0}\n",
                                __arglist(GetMemoryFlagNonVolatile(i)));
            }
            DebugStub.Print("\n\n\n");
        }

        // Dump Srat structure
        public void DumpSratStructure()
        {
            int offset = 12; // there are 12 bytes offset
            int processorCount = 0;
            int memoryCount = 0;
            int type,length;

            // fields
            uint ptype, plen, pdom, pid, pflag, peid, pdom2, pres;
            uint mtype, mlen, mdom, mres, mlow, mhigh, mlenl, mlenh;
            uint mres2, mflag, mres3;

            DebugStub.Print("  Region length {0}\n",
                            __arglist(region.Length));
            DebugStub.Print("------------------------------------\n");

            // reset counter
            while (offset < region.Length) {

                // this is a processor structure
                type = region.Read8(offset);
                if (type == ProcessorStructureId) {

                    length = region.Read8(offset+1);

                    DebugStub.Print("\n  proc:{0}  \n",
                                    __arglist(processorCount, length));
                    DebugStub.Print("------------------------------------\n");

                    ptype = region.Read8 (offset);
                    plen  = region.Read8 (offset+1);
                    pdom  = region.Read8 (offset+2);
                    pid   = region.Read8 (offset+3);
                    pflag = region.Read32(offset+4);
                    peid  = region.Read8 (offset+8);
                    pdom2 = region.Read32(offset+9);
                    pres  = region.Read32(offset+12);

                    DebugStub.Print("   ptype: {0}\n", __arglist(ptype));
                    DebugStub.Print("   plen : {0}\n", __arglist(plen ));
                    DebugStub.Print("   pdom : {0}\n", __arglist(pdom ));
                    DebugStub.Print("   pid  : {0}\n", __arglist(pid  ));
                    DebugStub.Print("   pflag: {0}\n", __arglist(pflag));
                    DebugStub.Print("   peid : {0}\n", __arglist(peid ));
                    DebugStub.Print("   pdom2: {0}\n", __arglist(pdom2));
                    DebugStub.Print("   pres : {0}\n", __arglist(pres ));


                    processorCount++;
                    offset += length;
                }

                // this is a memory structure
                else if (type == MemoryStructureId) {

                    length = region.Read8(offset+1);
                    DebugStub.Print("\n  memr:{0} \n",
                                    __arglist(memoryCount, length));
                    DebugStub.Print("------------------------------------\n");

                    mtype = region.Read8 (offset);
                    mlen  = region.Read8 (offset+1);
                    mdom  = region.Read32(offset+2);
                    mres  = region.Read8 (offset+6);
                    mlow  = region.Read32(offset+8);
                    mhigh = region.Read32(offset+12);
                    mlenl = region.Read32(offset+16);
                    mlenh = region.Read32(offset+20);
                    mres2 = region.Read32(offset+24);
                    mflag = region.Read32(offset+28);
                    mres3 = region.Read32(offset+32);

                    DebugStub.Print("   mtype: {0}\n", __arglist(mtype));
                    DebugStub.Print("   mlen : {0}\n", __arglist(mlen ));
                    DebugStub.Print("   mdom : {0}\n", __arglist(mdom ));
                    DebugStub.Print("   mres : {0}\n", __arglist(mres ));
                    DebugStub.Print("   mlow : {0}\n", __arglist(mlow ));
                    DebugStub.Print("   mhigh: {0}\n", __arglist(mhigh));
                    DebugStub.Print("   mlenl: {0}\n", __arglist(mlenl));
                    DebugStub.Print("   mlenh: {0}\n", __arglist(mlenh));
                    DebugStub.Print("   mres2: {0}\n", __arglist(mres2));
                    DebugStub.Print("   mflag: {0}\n", __arglist(mflag));
                    DebugStub.Print("   mres3: {0}\n", __arglist(mres3));

                    memoryCount++;
                    offset += length;
                }
                else {
                    DebugStub.Print("  Error \n");
                    DebugStub.Print("Impossible Affinity Structure Id\n");
                    DebugStub.Break();
                    break;
                }
            }

            DebugStub.Print("------------------------------------\n");
            DebugStub.Print("  Done Parsing Srat Structure ... \n");
            DebugStub.Print("  Found {0} processors and {1} memory\n",
                            __arglist(processorCount,memoryCount));
        }
    }
}

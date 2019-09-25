////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PageTableService.cs
//
//  Note:
//

using System;
using System.GCs;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using MemoryManager = Microsoft.Singularity.Memory.MemoryManager;

namespace Microsoft.Singularity.V1.Services
{
    [CLSCompliant(false)]
    public struct PageTableService
    {
        [ExternalEntryPoint]
        public static unsafe uint * GetPageTable()
        {
            uint * pageTable = MemoryManager.UserPageTable;

            Tracing.Log(Tracing.Debug, "PageTableService.GetPageTable() = {0:x8}",
                        (UIntPtr)pageTable);

            return pageTable;
        }

#if UINTPTR_SUPPORT_IN_ABI
        [ExternalEntryPoint]
        public static UIntPtr GetPageCount()
        {
            UIntPtr count = MemoryManager.UserPageCount;

            Tracing.Log(Tracing.Debug, "PageTableService.GetPageCount() = {0}",
                        count);

            return count;
        }

        [ExternalEntryPoint]
        public static UIntPtr GetBaseAddress()
        {
            UIntPtr addr = MemoryManager.UserBaseAddr;

            Tracing.Log(Tracing.Debug, "PageTableService.GetBaseAddress() = {0}",
                        addr);

            return addr;
        }
#endif

        [ExternalEntryPoint]
        public static uint GetProcessTag()
        {
            uint tag = Thread.CurrentProcess.ProcessTag;

            Tracing.Log(Tracing.Debug, "PageTableService.GetProcessTag() = {0}",
                        (UIntPtr)tag);

            return tag;
        }

        [ExternalEntryPoint]
        public static UIntPtr Allocate(UIntPtr bytes)
        {
            UIntPtr addr = MemoryManager.UserAllocate(
                MemoryManager.PagesFromBytes(bytes),
                Thread.CurrentProcess, 0, PageType.Unknown);

            Tracing.Log(Tracing.Debug,
                        "PageTableService.Allocate(bytes={0} addr={1:x8}",
                        bytes, addr);

            return addr;
        }

        [ExternalEntryPoint]
        public static UIntPtr AllocateIOMemory(UIntPtr limit,
                                               UIntPtr bytes,
                                               UIntPtr alignment)
        {
            UIntPtr addr = MemoryManager.AllocateIOMemory(
                limit, bytes, alignment, Thread.CurrentProcess);

            Tracing.Log(Tracing.Debug,
                        "PageTableService.AllocateIOMemory(limit={0:x}, bytes={1:x}, alignment={2:x}) addr= {3:x8}",
                        limit, bytes, alignment, addr);

            return addr;
        }

        [ExternalEntryPoint]
        public static void FreeIOMemory(UIntPtr addr,
                                        UIntPtr bytes)
        {
            Tracing.Log(Tracing.Debug, "PageTableService.FreeIOMemory(addr={0:x8}, bytes={1:x})",
                        addr, bytes);

            MemoryManager.FreeIOMemory(addr, bytes, Thread.CurrentProcess);
        }

        [ExternalEntryPoint]
        public static UIntPtr AllocateExtend(UIntPtr addr,
                                             UIntPtr bytes)
        {
            UIntPtr got = MemoryManager.UserExtend(
                addr, MemoryManager.PagesFromBytes(bytes),
                Thread.CurrentProcess, PageType.Unknown);

            Tracing.Log(Tracing.Debug,
                        "PageTableService.AllocateExtend(addr={0:x}, bytes={1:x}) addr={2:x8}",
                        addr, bytes, got);

            return got;
        }

        [ExternalEntryPoint]
        public static void Free(UIntPtr addr,
                                UIntPtr bytes)
        {
            Tracing.Log(Tracing.Debug, "PageTableService.Free(addr={0:x8}, bytes={1:x})",
                        addr, bytes);

            // We always round up block allocations to the nearest page,
            // so round up when freeing, too.
            MemoryManager.UserFree(addr,
                                   MemoryManager.PagesFromBytes(bytes),
                                   Thread.CurrentProcess);
        }

        [ExternalEntryPoint]
        public static unsafe bool QueryImpl(
            UIntPtr queryAddr,
            UIntPtr * regionAddr,
            UIntPtr * regionSize)
        {
            return Query(queryAddr, out *regionAddr, out *regionSize);
        }

        public static bool Query(UIntPtr queryAddr,
                                 out UIntPtr regionAddr,
                                 out UIntPtr regionSize)
        {
            PageType type = MemoryManager.UserQuery(
                queryAddr, out regionAddr, out regionSize);

            bool used = (type != PageType.Unknown);

            Tracing.Log(Tracing.Debug,
                        "PageTableService.Query(query={0:x8}, addr={1:x8}, size={2:x}) type={3}",
                        queryAddr, regionAddr, regionSize, (uint)type);

            return used;
        }

        [ExternalEntryPoint]
        public static unsafe void GetUsageStatisticsImpl(
            ulong * allocatedCount,
            ulong * allocatedBytes,
            ulong * freedCount,
            ulong * freedBytes)
        {
            GetUsageStatistics(out *allocatedCount, out *allocatedBytes,
                out *freedCount, out *freedBytes);
        }

        public static void GetUsageStatistics(out ulong allocatedCount,
                                              out ulong allocatedBytes,
                                              out ulong freedCount,
                                              out ulong freedBytes)
        {
            MemoryManager.GetUserStatistics(
                out allocatedCount,
                out allocatedBytes,
                out freedCount,
                out freedBytes);
        }

        //////////////////////////////////////////////////////////////////////
#if !UINTPTR_SUPPORT_IN_ABI
        [ExternalEntryPoint]
        public static uint GetPageCount()
        {
            uint count = (uint)MemoryManager.UserPageCount;

            Tracing.Log(Tracing.Debug, "PageTableService.GetPageCount() = {0:x8}",
                        count);

            return count;
        }

        [ExternalEntryPoint]
        public static uint GetBaseAddress()
        {
            uint addr = (uint)MemoryManager.UserBaseAddr;

            Tracing.Log(Tracing.Debug, "PageTableService.GetBaseAddress() = {0}",
                        addr);

            return addr;
        }

        [ExternalEntryPoint]
        public static uint Allocate(uint bytes)
        {
            uint addr = (uint)MemoryManager.UserAllocate(
                MemoryManager.PagesFromBytes(bytes),
                Thread.CurrentProcess, 0, PageType.Unknown);

            Tracing.Log(Tracing.Debug,
                        "PageTableService.Allocate(bytes={0} addr={1:x8}",
                        bytes, addr);

            return addr;
        }

        [ExternalEntryPoint]
        public static uint AllocateIOMemory(uint limit,
                                            uint bytes,
                                            uint alignment)
        {
            uint addr = (uint)MemoryManager.AllocateIOMemory(
                limit, bytes, alignment, Thread.CurrentProcess);

            Tracing.Log(Tracing.Debug,
                        "PageTableService.AllocateIOMemory(limit={0:x}, bytes={1:x}, alignment={2:x}) addr= {3:x8}",
                        limit, bytes, alignment, addr);

            return addr;
        }

        [ExternalEntryPoint]
        public static uint AllocateExtend(uint addr,
                                          uint bytes)
        {
            uint got = (uint)MemoryManager.UserExtend(
                addr, MemoryManager.PagesFromBytes(bytes),
                Thread.CurrentProcess, PageType.Unknown);

            Tracing.Log(Tracing.Debug,
                        "PageTableService.AllocateExtend(addr={0:x}, bytes={1:x}) addr={2:x8}",
                        addr, bytes, got);

            return addr;
        }

        [ExternalEntryPoint]
        public static void Free(uint addr,
                                uint bytes)
        {
            Tracing.Log(Tracing.Debug, "PageTableService.Free(addr={0:x8}, bytes={1:x})",
                        addr, bytes);

            // We always round up block allocations to the nearest page,
            // so round up when freeing, too.
            MemoryManager.UserFree(addr,
                                   MemoryManager.PagesFromBytes(bytes),
                                   Thread.CurrentProcess);
        }

        [ExternalEntryPoint]
        public static void FreeIOMemory(uint addr,
                                        uint bytes)
        {
            Tracing.Log(Tracing.Debug, "PageTableService.FreeIOMemory(addr={0:x8}, bytes={1:x})",
                        addr, bytes);

            MemoryManager.FreeIOMemory(addr, bytes, Thread.CurrentProcess);
        }

        [ExternalEntryPoint]
        public static unsafe bool QueryImpl(
            uint queryAddr,
            uint * regionAddr,
            uint * regionSize)
        {
            return Query(queryAddr, out *regionAddr, out *regionSize);
        }

        public static bool Query(uint queryAddr,
                                 out uint regionAddr,
                                 out uint regionSize)
        {
            UIntPtr ra;
            UIntPtr rs;

            PageType type = MemoryManager.UserQuery(
                queryAddr, out ra, out rs);

            bool used = (type != PageType.Unknown);

            regionAddr = (uint)ra;
            regionSize = (uint)rs;

            Tracing.Log(Tracing.Debug,
                        "PageTableService.Query(query={0:x8}, addr={1:x8}, size={2:x}) type={3}",
                        queryAddr, regionAddr, regionSize, (uint)type);

            return used;
        }
#endif
    }
}

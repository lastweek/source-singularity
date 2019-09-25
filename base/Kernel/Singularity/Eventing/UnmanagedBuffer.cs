////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   UnmanagedBuffer.cs
//
//  Note:
//

using System;
using System.Threading;
using System.Runtime.CompilerServices;

using Microsoft.Singularity;
using Microsoft.Singularity.V1.Services;    

namespace Microsoft.Singularity.Eventing
{
    [CLSCompliant(false)]
    public class UnmanagedMemoryBuffer {

        public UnmanagedMemoryBuffer Link;
        
        private ulong BufferSize;
        private unsafe byte * bufferMemory;

        public UnmanagedMemoryBuffer()
        {
            Link = null;
        }

        public unsafe byte * GetBuffer() {

            return bufferMemory;
        }

        public ulong GetSize() {

            return BufferSize;
        }

        public bool AllocateBuffer(ulong Size)
        {

            unsafe {
                
                //  Allocate the memory indicated as parameter, as nonGC

#if SINGULARITY_KERNEL
                UIntPtr pages = Microsoft.Singularity.Memory.MemoryManager.PagesFromBytes(Size);

                bufferMemory = (byte *)Microsoft.Singularity.Memory.MemoryManager.KernelAllocate(
                    pages, null, 0, System.GCs.PageType.NonGC).ToPointer();

                //  Allocation at page granularity. Preserve the actual size of the buffer
                BufferSize = (ulong)pages * Microsoft.Singularity.Memory.MemoryManager.PageSize;
                
#else  // !SINGULARITY_KERNEL
        
                bufferMemory = (byte *)PageTableService.Allocate(Size);
                BufferSize = Size;

#endif  //SINGULARITY_KERNEL

                if (bufferMemory == null) {

                    BufferSize = 0;
                    return false;
                }
            }

            return true;
        }
        
        ~UnmanagedMemoryBuffer()
        {
            unsafe {
                //  Allocate the memory indicated as parameter, as nonGC

#if SINGULARITY_KERNEL
                UIntPtr pages = Microsoft.Singularity.Memory.MemoryManager.PagesFromBytes(BufferSize);

                if (bufferMemory != null) {

                    Microsoft.Singularity.Memory.MemoryManager.KernelFree((UIntPtr)bufferMemory, pages, null);
                }

#else  // !SINGULARITY_KERNEL
        
                if (bufferMemory != null) {

                    PageTableService.Free((UIntPtr)bufferMemory, BufferSize);
                }

#endif  //SINGULARITY_KERNEL
            }
        }
        
    }
}


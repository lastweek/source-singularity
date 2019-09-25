////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MemoryStorage.cs
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
    [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
    public unsafe struct ArrayType {

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public ushort Length;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public ushort ItemSize;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public uint Type;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public void * Buffer;
    }


    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
    public class MemoryStorage : EventingStorage {

        private Mutex mutex;
        private UnmanagedMemoryBuffer Buffers;

        private LocalController hostController = null;

        ~MemoryStorage() 
        {
            Destroy();
        }

        unsafe public bool InitializeFromExistingHandle()
        {
            mutex = new Mutex();

            if (mutex == null) {

                return false;
            }

            // Mirror the existing memory buffer. We do not need actually to also fetch
            // the pointers since someone else has the ownership of that memory
            
            Buffers = new UnmanagedMemoryBuffer();
            hostController = Controller.GetLocalController();

            return (Buffers != null);
        }


        unsafe public bool Initialize(ulong Size)
        {
            mutex = new Mutex();

            if (mutex == null) {

                return false;
            }

            UnmanagedMemoryBuffer NewBuffer = new UnmanagedMemoryBuffer();

            if (NewBuffer != null) {

                uint overheadSize = MemoryStorage.GetMemoryStorageOveheadImpl();

                if (!NewBuffer.AllocateBuffer(overheadSize + Size)) {

                    return false;
                }
                
                Buffers = NewBuffer;

                StorageHandle = MemoryStorage.MemoryStorageCreateImpl(
                    QoS.StorageSettings,
                    NewBuffer.GetBuffer(), 
                    (uint)NewBuffer.GetSize(), 
                    0);

                if (Controller.GetLocalController().RegisterStorage( this )) {

                    hostController = Controller.GetLocalController();
                    
                    return true;
                }

            }
                
            return false;
        }

        public override bool AddBuffer(ulong Size)
        {
            unsafe {
                
                UnmanagedMemoryBuffer NewBuffer = new UnmanagedMemoryBuffer();

                if (NewBuffer != null) {

                    if (!NewBuffer.AllocateBuffer(Size)) {

                        return false;
                    }
                }
                
                mutex.AcquireMutex();
                NewBuffer.Link = Buffers;
                Buffers = NewBuffer;
                mutex.ReleaseMutex();

                MemoryStorage.MemoryStorageRegisterBufferImpl(StorageHandle, 
                                                              NewBuffer.GetBuffer(), 
                                                              (uint)NewBuffer.GetSize());
            }
            return true;
        }

        void Destroy() {

            if (hostController != null) {

                hostController.UnRegisterStorage(this);
            }
        }

        [NoHeapAllocation]
        public override unsafe UIntPtr CreateQueryView(bool forward)
        {
            return CreateQueryViewImpl(StorageHandle, forward);
        }

        [NoHeapAllocation]
        public override unsafe void DeleteQueryView(UIntPtr queryHandle)
        {
            DeleteQueryViewImpl(queryHandle);
        }

        public override UIntPtr GetNextEntry(UIntPtr queryHandle,
                                             ref QueryBuffer entryBuffer)
        {
            unsafe {

                UInt32 offset;
                UIntPtr type;
                
                fixed(byte * ptr = &(entryBuffer.GetBuffer()[0])) {

                    entryBuffer.EntryHandle =  MemoryStorage.GetNextEntryImpl(queryHandle , 
                                                                 &type,
                                                                 &offset, 
                                                                 ptr, 
                                                                 entryBuffer.GetBufferSize());

                    entryBuffer.Type = type;
                    entryBuffer.UserOffset = offset;

                    return entryBuffer.EntryHandle;
                }
            }
        }
        
        // ABI interfaces

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        static extern unsafe uint GetMemoryStorageOveheadImpl();

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        static extern unsafe UIntPtr MemoryStorageCreateImpl(uint Flags,
            byte * memoryBuffer, 
            uint bufferSize, 
            uint ZoneSize);
        
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        static extern unsafe void MemoryStorageRegisterBufferImpl(UIntPtr Storage, 
            byte * memoryBuffer, 
            uint bufferSize);
        
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr CreateQueryViewImpl(UIntPtr Storage, bool forward);

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe void DeleteQueryViewImpl(UIntPtr queryHandle);

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr WalkEventDescriptorImpl(UIntPtr eventHandle,
                                                             UIntPtr currentField,
                                                             UInt16 * offset,
                                                             UInt16 * type,
                                                             char * bufferName,
                                                             UInt16 bufferSize );

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr GetNextEntryImpl(UIntPtr queryHandle,
                                                     UIntPtr * type,
                                                     UInt32 * userOffset,
                                                     byte * buffer,
                                                     UInt16 bufferSize );
    }

    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
    public class GlobalStorage : EventingStorage {

        ~GlobalStorage() 
        {
            Destroy();
        }

        public GlobalStorage(UIntPtr storageId)
        {
            StorageHandle = DiagnosisService.OpenGlobalStorage(storageId);
        }

        void Destroy() {

            if (StorageHandle != 0) {
                
                DiagnosisService.CloseGlobalStorage(StorageHandle);
            }
        }

        [NoHeapAllocation]
        public override unsafe UIntPtr CreateQueryView(bool forward)
        {
            return DiagnosisService.CreateQueryView(StorageHandle, forward);
        }

        [NoHeapAllocation]
        public override unsafe void DeleteQueryView(UIntPtr queryHandle)
        {
            DiagnosisService.DeleteQueryView(queryHandle);
        }

        public override Controller GetController()
        {
            return Controller.GetSystemController();
        }

        public override UIntPtr GetNextEntry(UIntPtr queryHandle,
                                             ref QueryBuffer entryBuffer)
        {
            unsafe {

                UInt32 offset;
                UIntPtr type;
                
                fixed(byte * ptr = &(entryBuffer.GetBuffer()[0])) {

                    entryBuffer.EntryHandle =  DiagnosisService.GetNextEntry(queryHandle , 
                                                                 &type,
                                                                 &offset, 
                                                                 ptr, 
                                                                 entryBuffer.GetBufferSize());

                    entryBuffer.Type = type;
                    entryBuffer.UserOffset = offset;

                    return entryBuffer.EntryHandle;
                }
            }
        }
     }
}


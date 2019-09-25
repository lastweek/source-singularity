////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EventStorage.cs
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
    public struct QualityOfService {

        //  Maximum size of the user part of the events
        public uint EventMaximumSize;

        //  Number of events reserved. 0 means no reservation
        public uint ReservedEvents;

        [AccessedByRuntime("referenced in c++")]
        public const uint PermanentEvents = 1;
        [AccessedByRuntime("referenced in c++")]
        public const uint RecyclableEvents = 2;
        [AccessedByRuntime("referenced in c++")]
        public const uint ActiveEvents = 3;

        // OOM settings
        [AccessedByRuntime("referenced in c++")]
        public const uint OOM_GeneralFailure = 0x10;
        [AccessedByRuntime("referenced in c++")]
        public const uint OOM_DropNewEvents = 0x20;
        [AccessedByRuntime("referenced in c++")]
        public const uint OOM_BreakOnRecycle = 0x40;
        
        public uint StorageSettings;
        
        [AccessedByRuntime("referenced in c++")]
        public const uint ScopeUndefined = 0;
        [AccessedByRuntime("referenced in c++")]
        public const uint ScopeGlobal = 1;
        [AccessedByRuntime("referenced in c++")]
        public const uint ScopeLocal = 2;

        public uint StorageScope;
    }

    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
    public abstract class EventingStorage {

        public UIntPtr StorageHandle;
        public QualityOfService QoS;

        [AccessedByRuntime("referenced in c++")]
        public const uint EVENTING_STORAGE_FLAGS_ENABLED = 0x10000;
        [AccessedByRuntime("referenced in c++")]
        public const uint EVENTING_STORAGE_FLAGS_STACKTRACES = 2;

        public static EventingStorage CreateStorageFromHandle(UIntPtr handle) {

            MemoryStorage storage = new MemoryStorage();

            if (storage != null) {

                storage.QoS.StorageSettings = QualityOfService.PermanentEvents;
                storage.StorageHandle = handle;

                storage.InitializeFromExistingHandle();
            }

            return storage;
        }


        public static EventingStorage CreateLocalStorage(uint Flags, uint TotalSize) {

            MemoryStorage Storage = new MemoryStorage();

            if (Storage != null) {

                Storage.QoS.StorageSettings = Flags;

                Storage.Initialize(TotalSize);
            }

            return Storage;
        }

        public static EventingStorage OpenGlobalStorage(UIntPtr storageHandle) {

            return Controller.GetSystemController().OpenStorage(storageHandle);
        }



        [Inline]
        [NoHeapAllocation]
        public UIntPtr GetHandle(){

            return StorageHandle;
        }

        [NoHeapAllocation]
        public virtual bool CheckCompatible(QualityOfService qoS) {

            return (QoS.StorageSettings == qoS.StorageSettings) &&
                (QoS.StorageScope == qoS.StorageScope);
        }

        public virtual bool AddBuffer(ulong Size)
        {
            return false;
        }

        public virtual Controller GetController()
        {
            return Controller.GetLocalController();
        }

        [NoHeapAllocation]
        public abstract unsafe UIntPtr CreateQueryView(bool forward);

        [NoHeapAllocation]
        public abstract unsafe void DeleteQueryView(UIntPtr queryHandle);

        public abstract UIntPtr GetNextEntry(UIntPtr queryHandle,
                                             ref QueryBuffer entryBuffer);
    }
}

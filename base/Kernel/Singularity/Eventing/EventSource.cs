////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EventSource.cs
//
// 
//

using System;
using System.Threading;
using Microsoft.Singularity.Eventing;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.V1.Services;    

namespace Microsoft.Singularity.Eventing
{
    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
    public class EventSource 
    {
        public string SourceName;
        public EventingStorage Storage;
        public uint ControlFlags;
        public UIntPtr SourceHandle = 0;

        public Controller HostController;

        [AccessedByRuntime("referenced in c++")]
        public const uint CAPTURE_STACK_TRACE = 1;

        [AccessedByRuntime("referenced in c++")]
        public const uint CAPTURE_DEBUG_PRINT = 2;

        [AccessedByRuntime("referenced in c++")]
        public const uint ENABLE_ALL_MASK = 0xffff0000;

        ~EventSource()
        {
            HostController.UnRegisterSource(this);
        }

        public EventSource()
        {
        }

        public EventSource(Controller controller, string sourceName, UIntPtr storageHandle)
        {
            SourceName= sourceName;
            Storage = EventingStorage.CreateStorageFromHandle(storageHandle);
            ControlFlags = ENABLE_ALL_MASK;
            HostController = controller;
        }

        
        public EventSource(string sourceName, EventingStorage storage, uint controlFlags)
        {
            SourceName= sourceName;
            Storage = storage;
            ControlFlags = controlFlags;
            if (storage != null) {
                HostController = storage.GetController();
            } else {
                HostController = Controller.GetLocalController();
            }
        }

        public virtual void RegisterEnumSymbols()
        {
        }

        public virtual bool Register()
        {
            return (HostController != null) && HostController.RegisterSource(this);
        }

        [NoHeapAllocation]
        public unsafe UIntPtr LogEntry(uint Flags, UIntPtr eventType, byte * Buffer, int Size) {
        
            return LogSourceEntryImpl(SourceHandle, Flags, eventType, Buffer, Size);
        }

        [NoHeapAllocation]
        public unsafe UIntPtr LogEntry(uint Flags, UIntPtr eventType, byte * Buffer, int Size, 
                                                    int stringsCount, ArrayType * strings) 
        {
            return LogSourceEntryImpl(SourceHandle, Flags, eventType, Buffer, Size, stringsCount, strings);
        }
        
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        static public extern unsafe UIntPtr LogSourceEntryImpl(UIntPtr sourceHandle, 
                                                               uint Flags, 
                                                               UIntPtr eventType, 
                                                               byte * Buffer, 
                                                               int size);

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        static public extern unsafe UIntPtr LogSourceEntryImpl(UIntPtr sourceHandle, 
                                                               uint Flags, 
                                                               UIntPtr eventType, 
                                                               byte * Buffer, 
                                                               int size,
                                                               int arraysCount,
                                                               ArrayType * arrays);
    }

    [CLSCompliant(false)]
    public abstract class ActiveSource : EventSource 
    {
        public UIntPtr EventTypeHandle = 0;
        public UIntPtr DebugBufferAddress = 0;
        public ushort Count;
        public ushort EntrySize;

        public ActiveSource(string sourceName, int count, uint controlFlags)
            : base(sourceName, null, controlFlags)
        {
            HostController = Controller.GetLocalController();
            Count = (ushort)count;
        }

        public virtual unsafe bool GetActiveEntry(int index,
                                                       UIntPtr * type,
                                                       byte * buffer,
                                                       UInt16 bufferSize )
        {
            if ((index < 0) || (index >= Count) || (EntrySize > bufferSize)) {

                return false;
            }
            *type = EventTypeHandle;
            return true;
        }
    }
}


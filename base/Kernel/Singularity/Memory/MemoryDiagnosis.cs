////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MemoryDiagnosis.cs
//
//

using System;
using System.Threading;
using System.Runtime.CompilerServices;

using Microsoft.Singularity;
using Microsoft.Singularity.V1.Services;    
using Microsoft.Singularity.Eventing;
using System.Collections;

namespace Microsoft.Singularity.Eventing
{

    [CLSCompliant(false)]
    public class SystemAllocationLogger : EventSource {

        private const uint DefaultLogSize = 0x10000;

        public static SystemAllocationLogger Create(string sourceName) {

            EventingStorage storage = EventingStorage.CreateLocalStorage(QualityOfService.RecyclableEvents,
                                                                         DefaultLogSize);

            if (storage == null) {

                return null;                                                  
            }
            
            SystemAllocationLogger Logger  = new SystemAllocationLogger(sourceName, 
                                                                        storage,
                                                                        ENABLE_ALL_MASK);

            if (Logger != null) {

                Logger.Register();
            }

            return Logger;
        }


        //[EventType=Interrupt]
        [NoHeapAllocation]
        public bool Log(ushort processTag, ushort memoryType, UIntPtr address, UIntPtr size) {  // !!!!! this line must be entered to define a schema

    
            if ((ControlFlags & MemoryAllocation_Control_flag) != 0) {

                unsafe {

                    MemoryAllocationEvent memEvent; 

                    memEvent.MemoryType = memoryType;
                    memEvent.ProcessTag = processTag;
                    memEvent.Address = address;
                    memEvent.Size = size;

                    return (LogEntry(ControlFlags, 
                                      eventTypeMemoryAllocation, 
                                      (byte *)&memEvent, 
                                      sizeof(MemoryAllocationEvent)) != 0);
                }
            }
            
            return false;
        }

        public unsafe struct MemoryAllocationEvent {

            public UIntPtr Address;
            public UIntPtr Size;
            public ushort ProcessTag;
            public ushort MemoryType;
        };

        UIntPtr eventTypeMemoryAllocation;
        const uint MemoryAllocation_Control_flag = 0x10000;

        public override bool Register() {

            if (!base.Register()) {

                return false;
            }

            if (HostController.RegisterEvent("SystemMemoryAllocation", 
                                             "Memory allocation event: Address={0}, Memory type = {3}",
                                             ref eventTypeMemoryAllocation)) {

                HostController.RegisterEventField(eventTypeMemoryAllocation, 
                                                  "Address", 
                                                  0, 
                                                  DataType.__UIntPtr);

                HostController.RegisterEventField(eventTypeMemoryAllocation, 
                                                  "Size", 
                                                  0, 
                                                  DataType.__UIntPtr);

                HostController.RegisterEventField(eventTypeMemoryAllocation, 
                                                  "ProcessTag", 
                                                  0, 
                                                  DataType.__uint16);

                HostController.RegisterEventField(eventTypeMemoryAllocation, 
                                                  "MemoryType", 
                                                  0, 
                                                  DataType.__uint16);
                
            } else {

                // The event might have been registered already
                // Check whether we foundit already in the table or not

                if (eventTypeMemoryAllocation == 0) {
                    return false;
                }
            }

            return true;
        }

        SystemAllocationLogger (string sourceName, EventingStorage storage, uint controlFlags) 
            :base(sourceName, storage, controlFlags) {}
      
    }

    [CLSCompliant(false)]
    [NoCCtor]
    public class FreeMemoryDistribution : ActiveSource{

        //  Empty function declaration. Active counters are never logged through functions
        //  Present here for further usage with Phoenix codegen
        // [ActiveCounter]
        void TraceFreeBlock(UIntPtr BlockCount, UIntPtr TotalBlocksSize){}

        //  Here should start the codegen's work. Do it by hand for now

        public struct tmpFreeBlockEntry{

            public UIntPtr BlockCount;
            public UIntPtr TotalBucketSize;
        }

        internal tmpFreeBlockEntry[] Buffer;

        public static FreeMemoryDistribution Create(string sourceName, int size) {

            FreeMemoryDistribution Logger = new FreeMemoryDistribution(sourceName, size, ENABLE_ALL_MASK);

            if (Logger != null) {

                Logger.Register();
            }

            return Logger;
        }

        public override bool Register() {

            Buffer = new tmpFreeBlockEntry[Count];

            if (Buffer == null) {
                return false;
            }

            if (HostController.RegisterEvent("MemoryFreeBucket",
                                             "Memory free buckets: Count = {0}",
                                              ref EventTypeHandle)) {

                HostController.RegisterEventField(EventTypeHandle, 
                                                  "BlockCount", 
                                                  0, 
                                                  DataType.__UIntPtr);
                
                HostController.RegisterEventField(EventTypeHandle, 
                                                  "TotalBucketSize", 
                                                  0, 
                                                  DataType.__UIntPtr);
            } else {

                // The event might have been registered already
                // Check whether we foundit already in the table or not

                if (EventTypeHandle == 0) {
                    return false;
                }
            }

            unsafe {

                fixed (void * ptr = &Buffer[0]) {

                    DebugBufferAddress = (UIntPtr)ptr;
                }
            }

            // After all internal fields are setup, we can go ahead and register with the controller
            
            if (!base.Register()) {

                return false;
            }
                
            return true;
        }

        public tmpFreeBlockEntry this[int index]
        {
            get {
                return Buffer[index];
            }
        }

        public override unsafe bool GetActiveEntry(int index,
                                                       UIntPtr * type,
                                                       byte * buffer,
                                                       UInt16 bufferSize )
        {
            if (!base.GetActiveEntry(index, type, buffer, bufferSize)) {
                return false;
            }

            *(tmpFreeBlockEntry *)buffer = Buffer[index];
            return true;
        }

        FreeMemoryDistribution(string sourceName, int size, uint controlFlags) 
            :base(sourceName, size, controlFlags) 
        {
            unsafe {
                EntrySize = (ushort)sizeof(tmpFreeBlockEntry);
            }
        }
    }
}



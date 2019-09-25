////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EvProcessor.cs
//
//

using System;
using System.Threading;
using System.Runtime.CompilerServices;

using Microsoft.Singularity;
using Microsoft.Singularity.V1.Services;    
using Microsoft.Singularity.Eventing;
using Microsoft.Singularity.Isal;
using System.Collections;

namespace Microsoft.Singularity.Eventing
{
    [CLSCompliant(false)]
    public class ProcessorLogger : EventSource {


        private const uint DefaultProcessorLogSize = 0x10000;

        public static ProcessorLogger Create(string sourceName) {

            EventingStorage storage = EventingStorage.CreateLocalStorage(QualityOfService.RecyclableEvents,
                                                                         DefaultProcessorLogSize);

            if (storage == null) {

                return null;                                                  
            }
            
            ProcessorLogger Logger  = new ProcessorLogger(sourceName, 
                                                          storage,
                                                          CAPTURE_STACK_TRACE | ENABLE_ALL_MASK);

            if (Logger != null) {

                Logger.Register();
            }

            return Logger;
        }


        //[EventType=Interrupt]
        [NoHeapAllocation]
        public bool Log(int Vector) {  // !!!!! this line must be entered to define a schema

            // ???? GENCODE from here
    
    
            if ((ControlFlags & Interrupt_Control_flag) != 0) {

                unsafe {

                    InterruptEvent Event; 

                    Event.Vector = Vector;

                    return (LogEntry(ControlFlags, 
                                      eventTypeInterrupt, 
                                      (byte *)&Event, 
                                      sizeof(InterruptEvent)) != 0);
                }
            }
            
            return false;
        }

        public unsafe struct InterruptEvent {

            public int Vector;
        };

        UIntPtr eventTypeInterrupt;
        const uint Interrupt_Control_flag = 0x10000;


        public override bool Register() {

            if (!base.Register()) {

                return false;
            }

            if (HostController.RegisterEvent("Interrupt", 
                                             "Interrupt: Vector={0}",
                                             ref eventTypeInterrupt)) {

                HostController.RegisterEventField(eventTypeInterrupt, 
                                                                  "Vector", 
                                                                  0, 
                                                                  DataType.__int);
                
            } else {

                // The event might have been registered already
                // Check whether we foundit already in the table or not

                if (eventTypeInterrupt == 0) {
                    return false;
                }
            }

            return true;
        }

        ProcessorLogger(string sourceName, EventingStorage storage, uint controlFlags) 
            :base(sourceName, storage, controlFlags) {}
      
    }

    [CLSCompliant(false)]
    public class ProcessorCounter : ActiveSource{

        //[ActiveCounter]
        void InterruptCounter(int Hits){}

        // ???? CODEGEN from here

        //[ActiveCounter=InterruptCounter, ArraySize=256]
        public struct tmpInterruptCounter{

            public int Hits;
        }

        internal tmpInterruptCounter[] Buffer;

        public static ProcessorCounter Create(string sourceName, int size) {

            ProcessorCounter Logger = new ProcessorCounter(sourceName, size, ENABLE_ALL_MASK);

            if (Logger != null) {

                Logger.Register();
            }

            return Logger;
        }

        public override bool Register() {

            Buffer = new tmpInterruptCounter[Count];

            if (Buffer == null) {
                return false;
            }

            if (HostController.RegisterEvent("InterruptCounter",
                                             "InterruptCounter: Hits={0}",
                                             ref EventTypeHandle)) {

                HostController.RegisterEventField(EventTypeHandle, 
                                                                  "Hits", 
                                                                  0, 
                                                                  DataType.__int);
                
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

        public tmpInterruptCounter this[int index]
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

            *(tmpInterruptCounter *)buffer = Buffer[index];
            return true;
        }

        ProcessorCounter(string sourceName, int size, uint controlFlags) 
            :base(sourceName, size, controlFlags) 
        {
            unsafe {
                EntrySize = (ushort)sizeof(tmpInterruptCounter);
            }
        }
    }

    [CLSCompliant(false)]
    public class SamplingProfiler : EventSource {


        public static SamplingProfiler Create(string sourceName, int maxStackSize, uint storageSize) {

            EventingStorage storage = EventingStorage.CreateLocalStorage(QualityOfService.RecyclableEvents,
                                                                         storageSize);

            if (storage == null) {

                return null;                                                  
            }
            
            SamplingProfiler  Logger  = new SamplingProfiler(sourceName, 
                                                             maxStackSize,
                                                             storage,
                                                             ENABLE_ALL_MASK);
 
            if (Logger != null) {

                Logger.Register();
            }

            return Logger;
        }


        [NoHeapAllocation]
        public void LogStackTrace(UIntPtr eip, UIntPtr ebp) {
    
            if ((ControlFlags & Profile_Control_flag) != 0) {

                int actualStacks = 0;

                //
                // Capture the stack trace from the context
                //
                
                while (actualStacks < MaxStackSize) {

                    if (eip == 0) {
                        break;
                    }
                    
                    StackTrace[actualStacks++] = eip;

                    if (ebp == 0) {
                        break;
                    }
                    eip = Isa.GetFrameReturnAddress(ebp);
                    ebp = Isa.GetFrameCallerFrame(ebp);
                }

                //
                //  Setup the log structure and log the event
                //
                
                unsafe {

                    ProfilerEvent profilerEvent; 
                    profilerEvent.StackTrace = 1;

                    ArrayType arrayDescriptor;
 
                    fixed (UIntPtr * ptr = StackTrace) {
 
                        arrayDescriptor.ItemSize = (ushort)sizeof(UIntPtr);
                        arrayDescriptor.Length = (ushort)(actualStacks * arrayDescriptor.ItemSize);
                        arrayDescriptor.Type = DataType.__UIntPtr;
                        arrayDescriptor.Buffer = (void *)ptr;
                            
                        LogEntry(ControlFlags, 
                                  eventProfileType, 
                                  (byte *)&profilerEvent, 
                                  sizeof(ProfilerEvent),
                                  1,
                                  &arrayDescriptor);
                    }
                }
            }
        }

        public unsafe struct ProfilerEvent{
 
            public ushort StackTrace;
        };

        UIntPtr eventProfileType;
        const uint Profile_Control_flag = 0x10000;


        public override bool Register() {

            if (!base.Register()) {

                return false;
            }

            if (HostController.RegisterEvent("ProfileEvent", 
                                             "Profile event.",
                                             ref eventProfileType)) {
 
 
                HostController.RegisterEventField(eventProfileType, 
                                                  "StackTrace", 
                                                  0, 
                                                  DataType.__arrayType | DataType.__UIntPtr);
 
            } else {
 
                // The event might have been registered already
                // Check whether we foundit already in the table or not
 
                if (eventProfileType == 0) {
                    return false;
                }
            }
             return true;
        }

        UIntPtr [] StackTrace;
        int MaxStackSize;

        SamplingProfiler (string sourceName, int maxStackSize, EventingStorage storage, uint controlFlags) 
            :base(sourceName, storage, controlFlags) 
        {
            MaxStackSize = maxStackSize;
            StackTrace = new UIntPtr[maxStackSize];
        }
      
    }

}


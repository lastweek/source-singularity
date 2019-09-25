////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EventingKernel.cs
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
    [AccessedByRuntime("output to header : defined in EventController.cpp")]
    public class KernelController : LocalController {

        internal EventingStorage GeneralPurposeStorage;

        static public KernelController KernelControllerObject = null;

        internal override void Initialize() {

            if (KernelControllerObject != null) {

                //  Already initialized

                return;
            }

            base.Initialize();
            ProcessContext.Initialize();
            
            GeneralPurposeStorage = EventingStorage.CreateLocalStorage(QualityOfService.RecyclableEvents,
                    BUFFER_EXPANSION_SIZE);

            KernelControllerObject = this;
        }

        public override EventingStorage OpenStorage(UIntPtr storageHandle)
        {
            if (storageHandle == 0) {

                return GeneralPurposeStorage;
            }

            return new GlobalStorage(storageHandle);
        }

        
        public override void UnRegisterController(int processId)
        {
            Lock.AcquireMutex();
            ProcessContext ctx = ProcessContext.GetProcessContext(processId);
            
            if (ctx != null) {
                
                ctx.Delete();
            }

            Lock.ReleaseMutex();
        }

        public class ProcessContext {

            static Hashtable Clients;

            static public void Initialize() {

                Clients = new Hashtable();
            }

            uint ProcessId;
            UIntPtr ControllerHandle;
            UIntPtr Context;

            public bool Initialize(UIntPtr controllerHandle, UIntPtr context)
            {
                Clients[Thread.CurrentProcess.ProcessId] = this;
                
                ControllerHandle = controllerHandle;
                Context = context;

                if (!KernelController.RegisterExternalController(controllerHandle, context)) {

                    Clients.Remove(Thread.CurrentProcess.ProcessId);
                    return false;
                }

                return true;
            }

            [Inline]
            static public ProcessContext GetProcessContext(int processId)
            {
                return Clients[processId] as ProcessContext;
            }

            public void Delete()
            {
                if (ControllerHandle != 0) {
                    
                    DebugStub.WriteLine("UnregisterController {0}, {1}", __arglist(ControllerHandle, Context));
                    UnRegisterExternalController(ControllerHandle, Context);
                }
                
                ProcessId = 0;
                Clients.Remove(Thread.CurrentProcess.ProcessId);
            }
            
        }
            
        // System calls functions implementation.
        // TODO: Currently the handles passed to SIPs are actually the handles used by
        // the kernel. This must be changed to maintain a handle table for each SIP
        // and always use the conversion in these syscalls routines

        static public UIntPtr OpenStorageImpl(UIntPtr storageHandle)
        {
            if (storageHandle == 0) {
                
                //  Just return the kernel handle for now. 
                return KernelControllerObject.GeneralPurposeStorage.StorageHandle;
            } 

            // TODO: validate the handle against the existing list and
            // potential permissions. 

            return storageHandle;
        }

        public void CloseStorageImpl(UIntPtr storageHandle)
        {
            // See comments above for syscalls validations
            // There are no states maintained currently. Here will be however the
            // cleanup code for the storage returned to the process
        }
        
        public bool RegisterControllerImpl(UIntPtr controllerHandle, UIntPtr context)
        {
            ProcessContext ctx = new ProcessContext();
            
            if (ctx == null){

                return false;
            }

            Lock.AcquireMutex();
            bool success = ctx.Initialize(controllerHandle, context);
            Lock.ReleaseMutex();
            
            return success;
        }
    
        static public unsafe bool RegisterEventImpl(char * eventName, 
                                                    char * eventDescription, 
                                                    UIntPtr * eventHandle) 
        {
            UIntPtr handle = 0;

            string name = new string(eventName);
            string description = new string(eventDescription);
            
            bool success =  Controller.GetLocalController().RegisterEvent(name, 
                                                                          description, 
                                                                          ref handle);

            if (success) {

                *eventHandle = handle;
            }
            return success;
        }
            
        static public unsafe bool RegisterEventFieldImpl(UIntPtr eventHandle, 
            char * fieldName, 
            UInt16 offset, 
            UInt16 type) 
        {
            string name = new string(fieldName);

            return Controller.GetLocalController().RegisterEventField(eventHandle, 
                                                                      name, 
                                                                      offset, 
                                                                      type);
        }

        [NoHeapAllocation]
        static public unsafe UIntPtr LogSourceEntryImpl(UIntPtr storageHandle,
                                                        uint flags, 
                                                        UIntPtr eventType, 
                                                        byte * buffer, 
                                                        int size)
        {
            return EventSource.LogSourceEntryImpl(storageHandle,flags, eventType, buffer, size);
        }

        [NoHeapAllocation]
        static public unsafe UIntPtr LogSourceEntryImpl(UIntPtr storageHandle,
                                                        uint flags, 
                                                        UIntPtr eventType, 
                                                        byte * buffer, 
                                                        int size,
                                                        int arraysCount,
                                                        void ** arrays)
        {
            return EventSource.LogSourceEntryImpl(storageHandle,
                                                  flags, 
                                                  eventType, 
                                                  buffer, 
                                                  size, 
                                                  arraysCount, 
                                                  (ArrayType *)arrays);
        }

        [NoHeapAllocation]
        static public UIntPtr CreateQueryViewImpl(UIntPtr storageHandle, bool forward)
        {
            return MemoryStorage.CreateQueryViewImpl(storageHandle, forward);
        }

        [NoHeapAllocation]
        static public void DeleteQueryViewImpl(UIntPtr storageHandle)
        {
            MemoryStorage.DeleteQueryViewImpl(storageHandle);
        }
        
        static public unsafe UIntPtr GetNextEntryImpl(UIntPtr queryHandle,
                                                      UIntPtr * type,
                                                      UInt32 * userOffset,
                                                      byte * buffer,
                                                      UInt16 bufferSize )
        {
            return MemoryStorage.GetNextEntryImpl(queryHandle, 
                                                  type, 
                                                  userOffset, 
                                                  buffer, 
                                                  bufferSize);
        }

        public static unsafe bool RegisterEvent(char * eventName, 
                                                char * eventDescription, 
                                                UIntPtr * eventHandle) 
        {
            bool success;
            UIntPtr handle = 0;

            string name = new string(eventName);
            string description = new string(eventDescription);

            success = KernelControllerObject.RegisterEvent(name, description, ref handle);

            *eventHandle = handle;

            return success;
        }
            
        public static unsafe bool RegisterEventField(UIntPtr eventHandle, 
            char * fieldName, 
            UInt16 offset, 
            UInt16 type) {

            string name = new string(fieldName);
            
            return KernelControllerObject.RegisterEventField(eventHandle, 
                name, 
                offset, 
                type);
        }

        public static unsafe bool RegisterEventGenericField(UIntPtr eventHandle, 
                                                            char * fieldName, 
                                                            UInt16 offset, 
                                                            UInt16 size,
                                                            UIntPtr fieldTypeHandle) 
        {

            string name = new string(fieldName);
            
            return KernelControllerObject.RegisterEventGenericField(eventHandle, 
                                                                    name, 
                                                                    offset, 
                                                                    size,
                                                                    fieldTypeHandle);
        }

        public static unsafe bool RegisterEnum(char * enumName, 
                                               UInt16 type, 
                                               UIntPtr * eventHandle) 
        {
            bool success;
            UIntPtr handle = 0;

            string name = new string(enumName);

            success = KernelControllerObject.RegisterEnum(name, type, ref handle);

            *eventHandle = handle;

            return success;
        }
            
        public static unsafe bool RegisterEnumValue(UIntPtr eventHandle, 
                                                    char * valueName, 
                                                    UInt64 value, 
                                                    byte flagChar) 
        {

            string name = new string(valueName);
            
            return KernelControllerObject.RegisterEnumValue(eventHandle, 
                                                            name, 
                                                            value, 
                                                            flagChar);
        }

        public static unsafe UIntPtr WalkEventDescriptor(UIntPtr eventHandle,
                                                         UIntPtr currentField,
                                                         UInt16 * offset,
                                                         UInt16 * type,
                                                         char * bufferName,
                                                         UInt16 bufferSize )
        {
            return MemoryStorage.WalkEventDescriptorImpl(eventHandle, 
                                                         currentField, 
                                                         offset,
                                                         type,
                                                         bufferName,
                                                         bufferSize);
        }
        
        public static unsafe bool GetSourceInformation(UIntPtr sourceHandle,
                                                       UIntPtr * storageHandle,
                                                       UIntPtr * eventType,
                                                       UInt16 * count,
                                                       char * bufferName,
                                                       UInt16 bufferSize )
        {
            UIntPtr tmpStorageHandle = 0;
            UIntPtr tmpEventType = 0;
            UInt16 tmpCount = 0;
            String name = "";

            bool success = KernelControllerObject.GetSourceInformation(sourceHandle, 
                                                                      ref tmpStorageHandle, 
                                                                      ref tmpEventType, 
                                                                      ref tmpCount, 
                                                                      ref name);

            if (success) {

                *storageHandle = tmpStorageHandle;
                *eventType = tmpEventType;
                *count = tmpCount;

                String.LimitedFormatTo(name, new ArgIterator(), bufferName, bufferSize);
            }
            
            return success;
        }

        public static unsafe int QuerySourcesList(UIntPtr * buffer, int size)
        {
            int returnValue = 0;
            UIntPtr [] tmpBuffer = new UIntPtr[size];

            if (tmpBuffer != null) {

                returnValue = KernelControllerObject.QuerySourcesList(tmpBuffer, size);

                if (returnValue < size) {

                    size = returnValue;
                }

                for (int i = 0; i < size; i++) {

                    buffer[i] = tmpBuffer[i];
                }
            }

            return returnValue;
        }

        public static unsafe int QueryEventTypeList(UIntPtr * buffer, int size)
        {
            int returnValue = 0;
            UIntPtr [] tmpBuffer = new UIntPtr[size];

            if (tmpBuffer != null) {

                returnValue = KernelControllerObject.QueryEventTypeList(tmpBuffer, size);

                if (returnValue < size) {

                    size = returnValue;
                }

                for (int i = 0; i < size; i++) {

                    buffer[i] = tmpBuffer[i];
                }
            }

            return returnValue;
        }

        static public bool TestKernelStorageImpl()
        {
            TestKernelLogging.TestAllCases();
            return true;
        }

        //  ABI calls
        
        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe bool RegisterExternalController(UIntPtr controllerHandle, UIntPtr storageHandle);
        
        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe void UnRegisterExternalController(UIntPtr controllerHandle, UIntPtr storageHandle);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(512)]
        [NoHeapAllocation]
        public static extern unsafe bool DebugPrintLogEntry(UIntPtr controllerHandle, UIntPtr entryHandle);
        
    }
   
}



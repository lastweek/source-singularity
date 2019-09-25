////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EventingApp.cs
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
    //
    //  Proxy class to handle the system-scope controller functions
    //
    
    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in EventController.cpp")]
    public class SystemControllerProxy : Controller {

        UIntPtr ControllerHandle;
        UIntPtr ContextHandle;

        public override bool RegisterController()
        {
            unsafe {
                fixed(UIntPtr * ctr = &ControllerHandle, ctx =  &ContextHandle) {
                    
                    if (LocalController.GetControllerHandle(ctr, ctx)) {

                        return DiagnosisService.RegisterEventingController(ControllerHandle, 
                                                                           ContextHandle);
                    }
                }
            }
            return false;
        }

        public override UIntPtr WalkEventDescriptor(UIntPtr eventHandle,
                                                    UIntPtr currentField,
                                                    ref UInt16 offset,
                                                    ref UInt16 type,
                                                    ref string bufferName)
        {
            UInt16 tmpOffset;
            UInt16 tmpType;
            const UInt16 MaxBufferSize = 256;

            char[] tmpBufferName = new char[MaxBufferSize]; 

            unsafe {

                fixed(char* ptrBytes = &tmpBufferName[0]) {
                    
                    currentField = DiagnosisService.WalkEventDescriptor(eventHandle,
                                                                        currentField,
                                                                        &tmpOffset,
                                                                        &tmpType,
                                                                        ptrBytes,
                                                                        MaxBufferSize);

                    if (currentField != 0) {

                        string fieldName = "";

                        if (fieldName != null) {
                            for (int i = 0; i < MaxBufferSize; i++) {

                                if (tmpBufferName[i] == 0) {
                                    break;
                                }

                                fieldName += tmpBufferName[i];
                            }
                        }
                        type = tmpType;
                        offset = tmpOffset;
                        bufferName = fieldName;
                    }
                }
            }
            return currentField;
        }

        public override bool GetSourceInformation(UIntPtr sourceHandle,
                                                    ref UIntPtr storageHandle,
                                                    ref UIntPtr eventType,
                                                    ref UInt16 count,
                                                    ref string bufferName)
        {
            UIntPtr tmpStorageHandle;
            UIntPtr tmpType;
            UInt16 tmpCount;
            const UInt16 MaxBufferSize = 256;
            bool success = false;

            char[] tmpBufferName = new char[MaxBufferSize]; 

            if (tmpBufferName != null) {
                unsafe {

                    fixed(char* ptrBytes = &tmpBufferName[0]) {
                        
                        success = DiagnosisService.GetSourceInformation(sourceHandle,
                                                                        &tmpStorageHandle,
                                                                        &tmpType,
                                                                        &tmpCount,
                                                                        ptrBytes,
                                                                        MaxBufferSize);

                        if (success) {

                            string fieldName = "";

                            if (fieldName != null) {
                                for (int i = 0; i < MaxBufferSize; i++) {

                                    if (tmpBufferName[i] == 0) {
                                        break;
                                    }

                                    fieldName += tmpBufferName[i];
                                }
                            }
                            eventType = tmpType;
                            count = tmpCount;
                            storageHandle = tmpStorageHandle;
                            bufferName = fieldName;
                        }

                    }
                }
            }

            return success;
        }

        public override void UnRegisterController(int processId)
        {
        }

        public override EventingStorage OpenStorage(UIntPtr storageHandle)
        {
            GlobalStorage storage = new GlobalStorage(storageHandle);
            if ((storage == null) || (storage.GetHandle() == 0)) {

                return null;
            }

            return storage;
        }

        public override bool RegisterEvent(string eventName, 
                                           string eventDescription, 
                                           ref UIntPtr eventHandle) {

            unsafe {

                fixed (UIntPtr * ptr = &eventHandle) {
                    fixed (char * name = eventName) {
                        fixed (char * desc = eventDescription) {
                        
                            return DiagnosisService.RegisterEvent(name, desc, ptr);
                        }
                    }
                }
            }
        }
            
        public override bool RegisterEventField(UIntPtr eventHandle, 
            string fieldName, 
            UInt16 offset, 
            UInt16 type) {

            unsafe {
                fixed (char * name = fieldName) {
                    
                    return DiagnosisService.RegisterEventField(eventHandle, 
                                                               name, 
                                                               offset, 
                                                               type);
                }
            }
        }

        public override bool RegisterEventGenericField(UIntPtr eventHandle, 
                                                       string fieldName, 
                                                       UInt16 offset, 
                                                       UInt16 size,
                                                       UIntPtr fieldTypeHandle) 
        {
            unsafe {
                fixed (char * name = fieldName) {
                    
                    return DiagnosisService.RegisterEventGenericField(eventHandle, 
                                                                      name, 
                                                                      offset, 
                                                                      size,
                                                                      fieldTypeHandle);
                }
            }
        }

        //
        //  Enum support for applications
        //
        
        public override bool RegisterEnum(string enumName, 
                                          UInt16 type, 
                                          ref UIntPtr eventHandle) 
        {
            unsafe {

                fixed (UIntPtr * ptr = &eventHandle) {
                    fixed (char * name = enumName) {
                        
                        return DiagnosisService.RegisterEnum(name, type, ptr);
                    }
                }
            }
        }
            
        public override bool RegisterEnumValue(UIntPtr eventHandle, 
                                               string valueName, 
                                               UInt64 value, 
                                               byte flagChar) {

            unsafe {
                fixed (char * name = valueName) {
                    
                    return DiagnosisService.RegisterEnumValue(eventHandle, 
                                                              name, 
                                                              value, 
                                                              flagChar);
                }
            }
        }


        public override int QuerySourcesList(UIntPtr [] buffer, int size)
        {
            int totalItems = 0;

            unsafe {
                fixed (UIntPtr * ptr = buffer) {

                    totalItems = DiagnosisService.QuerySourcesList(ptr, size);
                }
            }
            return totalItems;
        }

        public override int QueryEventTypeList(UIntPtr [] buffer, int size)
        {
            int totalItems = 0;

            unsafe {
                fixed (UIntPtr * ptr = buffer) {

                    totalItems = DiagnosisService.QueryEventTypeList(ptr, size);
                }
            }
            return totalItems;
        }

        public override bool QueryActiveEntry(UIntPtr sourceHandle,
                                             int index,
                                             ref QueryBuffer entryBuffer)
        {
            unsafe {

                UInt32 offset;
                UIntPtr type;
                
                fixed(byte * ptr = &(entryBuffer.GetBuffer()[0])) {

                    bool success = DiagnosisService.ReadActiveSourceItem(sourceHandle, 
                                                                         index, 
                                                                         &type, 
                                                                         ptr, 
                                                                         entryBuffer.GetBufferSize());


                    entryBuffer.Type = type;

                    // the active entries do not have any header

                    entryBuffer.UserOffset = 0;

                    return success;
                }
            }
        }

        [AccessedByRuntime("referenced in c++")]
        [NoHeapAllocation]
        private static unsafe bool DebugPrintLogEntry(UIntPtr entryHandle )
        {
            return DiagnosisService.DebugPrintLogEntry(0, entryHandle);
        }


    }    
}



////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DiagnosisService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Eventing;

namespace Microsoft.Singularity.V1.Services
{
    [CLSCompliant(false)]
    public struct DiagnosisService
    {

        public static ulong SIPBufferSize = 0;
        public static ulong SIPProfileOptions = 0;
        
        public static ulong KernelBufferSize = 0;
        public static ulong KernelProfileOptions = 0;

        // External entry points

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe int GCProfileSettings(
            ulong *defaultMemorySize,
            ulong *Options
            )
        {

            *defaultMemorySize = SIPBufferSize;
            *Options = SIPProfileOptions;

            return 0;
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static bool RegisterEventingController(
            UIntPtr controllerHandle,
            UIntPtr executionContextHandle
            )
        {
            return KernelController.KernelControllerObject.RegisterControllerImpl(
                        controllerHandle, 
                        executionContextHandle);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static bool DebugPrintLogEntry(UIntPtr controllerHandle, UIntPtr entryHandle)
        {
            return KernelController.DebugPrintLogEntry(
                        controllerHandle, 
                        entryHandle);
        }
        
        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static bool TestKernelStorage()
        {
            return KernelController.TestKernelStorageImpl();
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static UIntPtr OpenGlobalStorage(UIntPtr storageHandle)
        {
            return KernelController.OpenStorageImpl(storageHandle);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static void CloseGlobalStorage(UIntPtr storageHandle)
        {
            KernelController.KernelControllerObject.CloseStorageImpl(storageHandle);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static unsafe UIntPtr LogSourceEntry(UIntPtr sourceHandle,
                                                    uint flags, 
                                                    UIntPtr eventType, 
                                                    byte * buffer, 
                                                    int size)
        {
            return KernelController.LogSourceEntryImpl(sourceHandle,
                                                       flags, 
                                                       eventType, 
                                                       buffer, 
                                                       size);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static unsafe UIntPtr LogSourceEntry(UIntPtr sourceHandle,
                                                    uint flags, 
                                                    UIntPtr eventType, 
                                                    byte * buffer, 
                                                    int size,
                                                    int stringsCount,
                                                    void ** strings)
        {
            return KernelController.LogSourceEntryImpl(sourceHandle,
                                                       flags, 
                                                       eventType, 
                                                       buffer, 
                                                       size, 
                                                       stringsCount, 
                                                       strings);
        }
        
        [ExternalEntryPoint]
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static UIntPtr CreateQueryView(UIntPtr storageHandle, bool forward)
        {
            return KernelController.CreateQueryViewImpl(storageHandle, forward);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static void DeleteQueryView(UIntPtr storageHandle)
        {
            KernelController.DeleteQueryViewImpl(storageHandle);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe UIntPtr GetNextEntry(UIntPtr queryHandle,
                                                  UIntPtr * type,
                                                  UInt32 * userOffset,
                                                  byte * buffer,
                                                  UInt16 bufferSize )
        {
            return KernelController.GetNextEntryImpl(queryHandle, 
                                                     type, 
                                                     userOffset, 
                                                     buffer, 
                                                     bufferSize);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe bool RegisterEvent(char * eventName, char * eventDescription, UIntPtr * eventHandle) {

            return KernelController.RegisterEvent(eventName, eventDescription, eventHandle);
        }
            
        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe bool RegisterEventField(UIntPtr eventHandle, 
                                                     char * fieldName, 
                                                     UInt16 offset, 
                                                     UInt16 type) {

            return KernelController.RegisterEventField(eventHandle, 
                                                       fieldName, 
                                                       offset, 
                                                       type);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe bool RegisterEventGenericField(UIntPtr eventHandle, 
                                                            char * fieldName, 
                                                            UInt16 offset, 
                                                            UInt16 size,
                                                            UIntPtr fieldTypeHandle) {

            return KernelController.RegisterEventGenericField(eventHandle, 
                                                              fieldName, 
                                                              offset, 
                                                              size,
                                                              fieldTypeHandle);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe bool RegisterEnum(char * enumName, UInt16 type, UIntPtr * eventHandle) 
        {

            return KernelController.RegisterEnum(enumName, type, eventHandle);
        }
            
        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe bool RegisterEnumValue(UIntPtr eventHandle, 
                                                    char * valueName, 
                                                    UInt64 value, 
                                                    byte flagChar) 
        {

            return KernelController.RegisterEnumValue(eventHandle, 
                                                     valueName, 
                                                     value, 
                                                     flagChar);
        }

        
        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe UIntPtr WalkEventDescriptor(UIntPtr eventHandle,
                                                         UIntPtr currentField,
                                                         UInt16 * offset,
                                                         UInt16 * type,
                                                         char * bufferName,
                                                         UInt16 bufferSize )
        {
            return KernelController.WalkEventDescriptor(eventHandle, 
                                                        currentField, 
                                                        offset,
                                                        type,
                                                        bufferName,
                                                        bufferSize);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe bool GetSourceInformation(UIntPtr sourceHandle,
                                                       UIntPtr * storageHandle,
                                                       UIntPtr * eventType,
                                                       UInt16 * count,
                                                       char * bufferName,
                                                       UInt16 bufferSize )
        {
            return KernelController.GetSourceInformation(sourceHandle, 
                                                         storageHandle, 
                                                         eventType, 
                                                         count, 
                                                         bufferName, 
                                                         bufferSize);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe int QuerySourcesList(UIntPtr * buffer, int size)
        {
            return KernelController.QuerySourcesList(buffer, size);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe int QueryEventTypeList(UIntPtr * buffer, int size)
        {
            return KernelController.QueryEventTypeList(buffer, size);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe bool ReadActiveSourceItem(UIntPtr sourceHandle,
                                                       int item,
                                                       UIntPtr * type,
                                                       byte * buffer,
                                                       UInt16 bufferSize )
        {
            return KernelController.KernelControllerObject.ReadActiveSourceItem(sourceHandle,
                                                                                item,
                                                                                type,
                                                                                buffer,
                                                                                bufferSize );
            
        }

        //  Wrap this up with a consistent definition with the SIP side
        //  we need to fix the silent drop of unsafe 
        public static int GCProfileSettingsImpl(
            out ulong defaultMemorySize,
            out ulong Options
            )
        {
            defaultMemorySize = KernelBufferSize;
            Options = KernelProfileOptions;

            return 0;
        }

        internal const uint DEFERED_COMMAND_ENABLE_KERNEL_GC = 1;
        internal const uint DEFERED_COMMAND_FORCE_GC_COLLECTION = 2;

        internal static uint DeferedCommand = 0;
        
        public static void DeferedUpdateNotification()
        {
            uint CapturedValue = DeferedCommand;

            DeferedCommand = 0;
            
            // TODO: This needs to be be moved later in a work item thread pool mechanism
            // of some sort
            
            if ((CapturedValue & DEFERED_COMMAND_ENABLE_KERNEL_GC) != 0) {
                // TODO: This API has disappeared in the arm branch 
                // - may need to get moved to a new API
                // GCProfilerLogger.StartProfiling();
            }

            if ((CapturedValue & DEFERED_COMMAND_FORCE_GC_COLLECTION) != 0) {
                DebugStub.WriteLine("Kernel GC collection started\n");
                System.GC.Collect();
                System.GC.WaitForPendingFinalizers();
                System.GC.Collect();
                DebugStub.WriteLine("Kernel GC collection completed\n");
                DebugStub.Break();
            }

        }
    }
}

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


namespace Microsoft.Singularity.V1.Services
{
    public struct DiagnosisService
    {
        int Reserved2;
        
        //
        // System call boundary must be unsafe to pass pointers
        // to basic types across the GC domains. But this should not be
        // directly accessable to application programs, but behind a
        // trusted safe wrapper that validates parameters and 
        // enforces type safety.
        //
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        internal static extern unsafe int GCProfileSettings(
            ulong *defaultMemorySize,
            ulong *Options
            );

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        internal static extern bool RegisterEventingController(
            UIntPtr controllerHandle,
            UIntPtr executionContextHandle
        );

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        internal static extern bool DebugPrintLogEntry(UIntPtr controllerHandle, 
                                                       UIntPtr entryHandle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        internal static extern bool TestKernelStorage();


        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern UIntPtr OpenGlobalStorage(UIntPtr storageId);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void CloseGlobalStorage(UIntPtr storageHandle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe UIntPtr LogSourceEntry(UIntPtr sourceHandle,
                                                           uint flags, 
                                                           UIntPtr eventType, 
                                                           byte * buffer, 
                                                           int size);
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe UIntPtr LogSourceEntry(UIntPtr sourceHandle,
                                                           uint flags, 
                                                           UIntPtr eventType, 
                                                           byte * buffer, 
                                                           int size,
                                                           int stringsCount,
                                                           void ** strings);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern UIntPtr CreateQueryView(UIntPtr storageHandle, bool forward);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void DeleteQueryView(UIntPtr storageHandle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe UIntPtr GetNextEntry(UIntPtr queryHandle,
                                                         UIntPtr * type,
                                                         UInt32 * userOffset,
                                                         byte * buffer,
                                                         UInt16 bufferSize );


        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool RegisterEvent(char * eventName, 
                                                       char * eventDescription, 
                                                       UIntPtr * eventHandle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool RegisterEventField(UIntPtr eventHandle, 
            char * fieldName, 
            UInt16 offset, 
            UInt16 type);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool RegisterEventGenericField(UIntPtr eventHandle, 
                                                                   char * fieldName, 
                                                                   UInt16 offset, 
                                                                   UInt16 size,
                                                                   UIntPtr fieldTypeHandle);


        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool RegisterEnum(char * enumName, UInt16 type, UIntPtr * eventHandle);
            
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool RegisterEnumValue(UIntPtr eventHandle, 
                                                            char * valueName, 
                                                            UInt64 value, 
                                                            byte flagChar);
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe UIntPtr WalkEventDescriptor(UIntPtr eventHandle,
                                                                UIntPtr currentField,
                                                                UInt16 * offset,
                                                                UInt16 * type,
                                                                char * bufferName,
                                                                UInt16 bufferSize );
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetSourceInformation(UIntPtr sourceHandle,
                                                              UIntPtr * storageHandle,
                                                              UIntPtr * eventType,
                                                              UInt16 * count,
                                                              char * bufferName,
                                                              UInt16 bufferSize );

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe int QuerySourcesList(UIntPtr * buffer, int size);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe int QueryEventTypeList(UIntPtr * buffer, int size);
        
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool ReadActiveSourceItem(UIntPtr sourceHandle,
                                                              int item,
                                                              UIntPtr * type,
                                                              byte * buffer,
                                                              UInt16 bufferSize );

        //
        // The signature offered to our caller is safe
        //
        public static int GCProfileSettingsImpl(
            out ulong defaultMemorySize,
            out ulong Options
            )
        {
            int retval;

            // This keeps unsafe blocks well contained
            unsafe {

                //
                // Note: Would it be more efficient to declare local stack
                //       variables and reference these under fixed rather
                //       than locking the caller supplied references which
                //       may point to class fields and involve more complicated
                //       GC interactions?
                //
                fixed (ulong* 
                       pdefaultMemorySize = &defaultMemorySize,
                       pOptions = &Options
                       ) {

                    retval = DiagnosisService.GCProfileSettings(
                         pdefaultMemorySize,
                         pOptions
                         );
                }
            }

            return retval;
        }
    }
}

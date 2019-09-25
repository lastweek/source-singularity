////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EventController.cs
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
    //  Define here the controller class. A controller object
    //  defines the scope of the tracing / eventing, 
    //  defines the lifetime of the eventing related metadata such as
    //  event types, sources and consumers, and implicitely
    //  respects the isolation boundary for events. Queries and 
    //  traces accross controllers should use contracts. Queries / logging
    //  from SIPs to kernel use syscalls ABIs
    //

    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in EventController.cpp")]
    public abstract class Controller {

        //  Commonly all events / traces are using by default the local controller
        //  A SIP and kernel has the optional to instantiate additional controllers.

        internal static LocalController LocalControllerObject;

        //  Some events may choose for a system-wide visibility, in which case
        //  a SIP may refer through a system controller. For kernel, both system and
        //  local controller are the same.
        
        internal static Controller SystemControllerObject;

        //  default size for entry enumerations
        
        const ushort DefaultEntrySize = 256;

        //
        //  Define the accessor methods to the system and local controller
        //

        static public LocalController GetLocalController()
        {
            return LocalControllerObject;
        }

        static public Controller GetSystemController()
        {
            return SystemControllerObject;
        }

        static public bool IsSystemScope()
        {
#if SINGULARITY_KERNEL

            return true;

#else // SINGULARITY_KERNEL

            return false;

#endif // SINGULARITY_KERNEL
            
        }

        //  Public methods

        static public void InitializeSystem() {

            // Create the system controller if needed. The SIPs will
            // get a proxy controller object that will handle operations
            // as syscalls. 
            // TODO: Further optimizations may allow writing a more
            // efficient proxy that may use shared memory.

#if SINGULARITY_KERNEL

            KernelController controller = new KernelController();

            if (controller != null) {

                LocalControllerObject = controller;
                SystemControllerObject = LocalControllerObject;
                controller.Initialize();
            }
#else
            LocalController controller = new LocalController();

            if (controller != null) {

                LocalControllerObject = controller;

                //  For SIPs we need a proxy object that will handle the calls
                //  to the system controller

                SystemControllerObject = new SystemControllerProxy();
                
                controller.Initialize();
            }

#endif
            if (SystemControllerObject != null) {

                SystemControllerObject.Initialize();
                SystemControllerObject.RegisterController();
                QuerySession.InitializeQuerySystem();
            }

        }

        //  Avoid any cleanup that would normally happen when a storage is deleted or
        //  a source is de-registered during SIP shutdown. Beside the work is unnecessary,
        //  there are problems with the order of executing the finalizers at shutdown 
        
        internal static bool Finalized = false;
        
        static public void Finalize() {
            Finalized = true;
        }

        //  Private fields
        
        internal Mutex Lock;

        //
        //  Abstract methods
        //

        public abstract bool RegisterEvent(string eventName, 
                                           string eventDescription, 
                                           ref UIntPtr eventHandle);
        
        public abstract bool RegisterEventField(UIntPtr eventHandle, 
                                                string fieldName, 
                                                UInt16 offset, 
                                                UInt16 type);

        public abstract bool RegisterEventGenericField(UIntPtr eventHandle, 
                                                       string fieldName, 
                                                       UInt16 offset, 
                                                       UInt16 size,
                                                       UIntPtr fieldTypeHandle);

        public abstract bool RegisterEnum(string enumName, 
                                          UInt16 type, 
                                          ref UIntPtr eventHandle);
        
        public abstract bool RegisterEnumValue(UIntPtr eventHandle, 
                                               string valueName, 
                                               UInt64 value, 
                                               byte flagChar);
        
        public abstract UIntPtr WalkEventDescriptor(UIntPtr eventHandle,
                                                    UIntPtr currentField,
                                                    ref UInt16 offset,
                                                    ref UInt16 type,
                                                    ref string bufferName);

        public abstract bool GetSourceInformation(UIntPtr sourceHandle,
                                                    ref UIntPtr storageHandle,
                                                    ref UIntPtr eventType,
                                                    ref UInt16 count,
                                                    ref string bufferName);

        //  Virtual methods
        
        internal virtual void Initialize()
        {
            Lock = new Mutex();
        }

        //
        //  Controller related methods
        //
        
        public virtual bool RegisterController()
        {
            return true;
        }

        public virtual void UnRegisterController(int processId)
        {
        }

        //
        //  Storage related methods
        //

        public virtual EventingStorage OpenStorage(UIntPtr storageHandle) 
        {
            return null;
        }

        //
        //  Source related methods
        //

        public virtual bool RegisterSource(EventSource source)
        {
            return false;
        }
        
        public virtual void UnRegisterSource(EventSource source){}


        //
        //  Query functionality methods
        //
        
        public virtual int QuerySourcesList(UIntPtr [] buffer, int size)
        {
            return 0;
        }

        public virtual int QueryEventTypeList(UIntPtr [] buffer, int size)
        {
            return 0;
        }

        public virtual bool QueryActiveEntry(UIntPtr sourceHandle,
                                             int index,
                                             ref QueryBuffer entryBuffer)
        {
            return false;
        }

        public virtual void EnumerateActiveSources(QuerySourceDelegate sourceDelegate,
                                                   ActiveSourceEntryDelegate activeEntryDelegate,
                                                   QueryEntryDelegate entryDelegate,
                                                   ushort maxEntrySize,
                                                   ref EnumerationContext context)
        {

            if (maxEntrySize == 0) {
                maxEntrySize = DefaultEntrySize;
            }

            //  Create a temporary buffer to store the temporary query information
            
            QueryBuffer entryBuffer = new QueryBuffer(maxEntrySize);

            if ((entryBuffer == null) || (sourceDelegate == null)) {
                return;
            }

            //  Prepare to query the controller for the source list. We just pick up an number
            //  that would represent the limit for most common cases as the initial guess.

            int currentSize = 100;
            UIntPtr [] sourceArray = new UIntPtr[currentSize];

            if (sourceArray != null) {

                //  Query the controller for the actual source list

                int sourceCount = QuerySourcesList(sourceArray, currentSize);

                //
                //  The array was not large enough, attempt again with the new size

                while (sourceCount > currentSize) {

                    sourceArray = new UIntPtr[sourceCount];
                    sourceCount = QuerySourcesList(sourceArray, currentSize);
                }

                //
                //  We sucessfully received an array of entries. We walk them and build the
                //  required information
                //
                
                for (int i = 0; i < sourceCount; i++) {
                    
                    UIntPtr sourceHandle = sourceArray[i];
                    UIntPtr storageHandle = 0;
                    UIntPtr eventType = 0;
                    UInt16 count = 0;
                    string bufferName = "";

                    if (GetSourceInformation(sourceHandle, 
                                             ref storageHandle, 
                                             ref eventType, 
                                             ref count, 
                                             ref bufferName)) {

                        if (storageHandle == 0) {

                            //
                            //  This is an active source. The eventing has no information
                            //  about the storage, it has instead information about the
                            //  types of events handled by this source
                            //

                            EventDescriptor descriptor = QuerySession.GetEventDescriptor(this, 
                                                                                         eventType);

                            if (descriptor != null) {

                                //  The source is valid, call the delegate with the appropriate
                                //  arguments filled in
                                // TODO: Also retrieve the control flags status
                                

                                if (!sourceDelegate(sourceHandle, 
                                                    storageHandle, 
                                                    eventType, 
                                                    count, 
                                                    bufferName, 
                                                    descriptor, 
                                                    ref context)) {
                                    break;
                                }
                                
                                if (entryDelegate != null) {

                                    //  The caller also provided an entry delegate. We need in that
                                    //  case to also enumerate all entries from the active source

                                    for (int index = 0; index < count; index++) {

                                        if (!QueryActiveEntry(sourceHandle, 
                                                              index, 
                                                              ref entryBuffer)) {
                                            break;
                                        }

                                        activeEntryDelegate(sourceHandle, 
                                                            index, 
                                                            descriptor, 
                                                            entryBuffer, 
                                                            ref context);
                                    }
                                }
                            }
                        } else {

                            //  This source has an associated storage. Enumerate the entries from
                            //  the storage
                            // TODO: we might also want to filter the sources inside the storage
                            // since multiple sources can share the same storage

                            if (!sourceDelegate(sourceHandle, 
                                                storageHandle, 
                                                eventType, 
                                                count, 
                                                bufferName, 
                                                null, 
                                                ref context)) {
                                break;
                            }
                            
                            EventingStorage storage = OpenStorage(storageHandle);

                            if (storage != null) {

                                // Instantiate a query session for the storage and
                                // enumerate the entries passing the provided delegate

                                QuerySession query = new QuerySession();
                                
                                if ((query != null) && (context != null) && 
                                     query.Initialize(storage, false)) {

                                    query.EnumerateEntries(entryDelegate, ref context);
                                }
                            }
                        }

                    }
                }
            }
        }

        public static unsafe bool GetSharedSourceHandles(uint infoId,
                                                         out UIntPtr storageHandle, 
                                                         out UIntPtr sourceHandle, 
                                                         out UIntPtr eventTypeHandle )
        {

            if ((infoId == TracingInfo) || (infoId == MonitoringInfo)) {

                UIntPtr tmpStorageHandle;
                UIntPtr tmpSourceHandle;
                UIntPtr tmpEventTypeHandle;

                if (GetSharedSourceHandlesInternal(infoId, 
                                                   &tmpStorageHandle, 
                                                   &tmpSourceHandle, 
                                                   &tmpEventTypeHandle)) {

                    storageHandle = tmpStorageHandle;
                    sourceHandle = tmpSourceHandle;
                    eventTypeHandle = tmpEventTypeHandle;

                    return true;
                }
            }

            storageHandle = 0;
            sourceHandle = 0;
            eventTypeHandle = 0;

            return false;
        }

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        public const uint TracingInfo = 1;

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        public const uint MonitoringInfo = 2;
        
        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe bool GetSharedSourceHandlesInternal(uint infoId,
                                                                        UIntPtr * storageHandle, 
                                                                        UIntPtr * sourceHandle, 
                                                                        UIntPtr * eventTypeHandle );
    }

    
    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in EventController.cpp")]
    public class LocalController : Controller {

        //
        // Internal fields
        //

        //  The type repository is a permanent
        
        internal EventingStorage TypesRepository;
        internal Hashtable EventTable;
        internal Hashtable SourcesHandleTable;
        internal Hashtable SourcesLookupTable;

        internal ControllerLogger InternalSource;

        internal const uint BUFFER_EXPANSION_SIZE = 0x10000;

        //  Public methods

        //  Private methods
        
        internal override void Initialize() {

            base.Initialize();
            
            EventTable = new Hashtable();
            SourcesLookupTable = new Hashtable();
            SourcesHandleTable = new Hashtable();

            UIntPtr RepositoryStorageHandle = FetchLocalStorage();

            if (RepositoryStorageHandle != 0) {
                
                TypesRepository = EventingStorage.CreateStorageFromHandle(RepositoryStorageHandle);

                //  Fetch now the existing source list created before initializing the controller

                int currentSize = 20;
                UIntPtr [] sourceArray = new UIntPtr[currentSize];

                if (sourceArray != null) {

                    unsafe {
                        fixed(UIntPtr * ptr = sourceArray) {

                            int sourceCount = QuerySystemSources(ptr, (ushort)currentSize);

                            while (sourceCount > currentSize) {

                                sourceArray = new UIntPtr[sourceCount];
                                sourceCount = QuerySystemSources(ptr, (ushort)currentSize);
                            }

                            for (int i = 0; i < sourceCount; i++) {

                                UIntPtr sourceHandle = sourceArray[i];
                                UIntPtr storageHandle = 0;
                                string bufferName = "";

                                if (GetNativeSourceName(sourceHandle, ref storageHandle, ref bufferName)) {

                                    EventSource source = new EventSource(this, bufferName, storageHandle);
                                    
                                    if (source != null) {
                                        source.Register();
                                    }
                                }
                            }
                        }
                    }

                }
                
            } else {

                TypesRepository = EventingStorage.CreateLocalStorage(QualityOfService.PermanentEvents,
                                                                     BUFFER_EXPANSION_SIZE);
                SetRepositoryStorage(TypesRepository.GetHandle());
            }
                
            string sourceName = "ControllerLog";
            
#if SINGULARITY_KERNEL

            sourceName = sourceName + "{kernel}";

#else
            unsafe {

                int argMaxLen = ProcessService.GetStartupArg(0, null, 0);
                char[] argArray = new char [argMaxLen];

            
                fixed (char *argptr = &argArray[0]) {
                    int len = ProcessService.GetStartupArg(0,
                                                           argptr,
                                                           argArray.Length);
                    sourceName = sourceName + "{"+String.StringCTOR(argptr, 0, len)+"}";
                    sourceName = sourceName + "(PID:"+ ProcessService.GetCurrentProcessId() +")";
                }
            }
#endif

            InternalSource = ControllerLogger.Create(sourceName, TypesRepository);
        }

        //  Event schema registration routines
        
        public override bool RegisterEvent(string eventName, 
                                           string eventDescription, 
                                           ref UIntPtr eventHandle) {

            Lock.AcquireMutex();
            object o = EventTable[eventName];
            
            if (o != null) {

                // Type already registered. Return the existing value
                eventHandle = (UIntPtr)o;
                Lock.ReleaseMutex();
                return false;
            }

            eventHandle = RegisterEventDescriptorInternal(eventName, eventDescription);

            while (eventHandle == 0) {

                if (!TypesRepository.AddBuffer(BUFFER_EXPANSION_SIZE)) {

                    Lock.ReleaseMutex();
                    return false;
                }

                eventHandle = RegisterEventDescriptorInternal(eventName, eventDescription);
            }

            EventTable[eventName] = eventHandle;
            
            Lock.ReleaseMutex();

            return true;
        }
            
        public override bool RegisterEventField(UIntPtr eventHandle, 
                                                string fieldName, 
                                                UInt16 offset, 
                                                UInt16 type) {

            UIntPtr field = RegisterEventFieldInternal(eventHandle, 
                fieldName, 
                offset, 
                type);

            while (field == 0) {

                Lock.AcquireMutex();
                if (!TypesRepository.AddBuffer(BUFFER_EXPANSION_SIZE)) {

                    Lock.ReleaseMutex();
                    return false;
                }

                Lock.ReleaseMutex();
                
                field = RegisterEventFieldInternal(eventHandle, 
                    fieldName, 
                    offset, 
                    type);
            }

            return true;
        }

        public override bool RegisterEventGenericField(UIntPtr eventHandle, 
                                                       string fieldName, 
                                                       UInt16 offset, 
                                                       UInt16 size,
                                                       UIntPtr fieldTypeHandle) {

            UIntPtr field = RegisterEventGenericFieldInternal(eventHandle, 
                                                              fieldName, 
                                                              offset,
                                                              size,
                                                              fieldTypeHandle);

            while (field == 0) {

                Lock.AcquireMutex();
                if (!TypesRepository.AddBuffer(BUFFER_EXPANSION_SIZE)) {

                    Lock.ReleaseMutex();
                    return false;
                }

                Lock.ReleaseMutex();
                
                field = RegisterEventGenericFieldInternal(eventHandle, 
                                                          fieldName, 
                                                          offset,
                                                          size,
                                                          fieldTypeHandle);
            }

            return true;
        }

        //
        //  Enumeration registration support
        //
        
        public override bool RegisterEnum(string enumName, 
                                          UInt16 type, 
                                          ref UIntPtr eventHandle) {

            Lock.AcquireMutex();
            object o = EventTable[enumName];
            
            if (o != null) {

                // Type already registered. Return the existing value
                eventHandle = (UIntPtr)o;
                Lock.ReleaseMutex();
                return false;
            }

            eventHandle = RegisterEnumDescriptorInternal(enumName, type);

            while (eventHandle == 0) {

                if (!TypesRepository.AddBuffer(BUFFER_EXPANSION_SIZE)) {

                    Lock.ReleaseMutex();
                    return false;
                }

                eventHandle = RegisterEnumDescriptorInternal(enumName, type);
            }

            EventTable[enumName] = eventHandle;
            
            Lock.ReleaseMutex();

            return true;
        }
            
        public override bool RegisterEnumValue(UIntPtr eventHandle, 
                                               string valueName, 
                                               UInt64 value, 
                                               byte flagChar) {

            UIntPtr field = RegisterValueDescriptorInternal(eventHandle, 
                                                            valueName, 
                                                            value, 
                                                            flagChar);

            while (field == 0) {

                Lock.AcquireMutex();
                if (!TypesRepository.AddBuffer(BUFFER_EXPANSION_SIZE)) {

                    Lock.ReleaseMutex();
                    return false;
                }

                Lock.ReleaseMutex();
                field = RegisterValueDescriptorInternal(eventHandle, 
                                                        valueName, 
                                                        value, 
                                                        flagChar);
            }

            return true;
        }

        //  Storage registration routines
        
        public bool RegisterStorage(EventingStorage Storage)
        {
            Lock.AcquireMutex();
            bool success = RegisterStorageImpl(Storage.GetHandle());
            Lock.ReleaseMutex();
            return success;
         }
    
        public void UnRegisterStorage(EventingStorage Storage)
        {
            if (!Controller.Finalized) {
                
                Lock.AcquireMutex();
                UnRegisterStorageImpl(Storage.GetHandle());
                Lock.ReleaseMutex();
            }
        }

        // Eventing source support routines

        public override bool RegisterSource(EventSource source)
        {
            // Sanity check against double registration
            if (source.SourceHandle != 0) {
                return false;
            }
            
            UIntPtr sourceHandle= 0;

            Lock.AcquireMutex();

            object obj = SourcesLookupTable[source.SourceName];

            if (obj != null) {

                sourceHandle = (UIntPtr)obj;
            }
            
            if (sourceHandle != 0) {

                object existingSource = SourcesHandleTable[sourceHandle];

                if (existingSource != null) {
                    
                    // Type already registered. Return the existing value
                    Lock.ReleaseMutex();
                    return false;
                }
            } else {

                // The handle for this source has not been allocated
                // Register a new one

                sourceHandle = AllocateSourceHandleImpl(source.SourceName);
                
                while (sourceHandle == 0) {

                    if (!TypesRepository.AddBuffer(BUFFER_EXPANSION_SIZE)) {

                        Lock.ReleaseMutex();
                        return false;
                    }

                    sourceHandle = AllocateSourceHandleImpl(source.SourceName);
                }

                SourcesLookupTable[source.SourceName] = sourceHandle;
            }

            // We must have here a valid source handle

            source.SourceHandle = sourceHandle;
            SourcesHandleTable[sourceHandle] = source;

            ActiveSource activeSource = source as ActiveSource;

            if (activeSource == null) {

                //  regular sources with associated memory storage

                RegisterSourceStorageImpl(sourceHandle, 
                                          source.Storage.GetHandle(), 
                                          source.ControlFlags);
                
            } else {

                RegisterActiveSourceImpl(sourceHandle, 
                                         activeSource.EventTypeHandle,
                                         activeSource.DebugBufferAddress,
                                         activeSource.Count,
                                         activeSource.EntrySize);

                //  Active sources, the object does the event buffer management
            }

            Lock.ReleaseMutex();
            return true;
        }
        
        public override void UnRegisterSource(EventSource source)
        {
            if (!Controller.Finalized) {
                Lock.AcquireMutex();
                
                if (source.SourceHandle != 0) {

                    SourcesHandleTable.Remove(source.SourceHandle);
                    UnRegisterSourceImpl(source.SourceHandle);

                    source.SourceHandle = 0;
                }
                Lock.ReleaseMutex();
            }
        }
        public override int QuerySourcesList(UIntPtr [] buffer, int size)
        {
            int i = 0;
            Lock.AcquireMutex();

            IDictionaryEnumerator enumerator = SourcesHandleTable.GetEnumerator();
            while (enumerator.MoveNext()) {

                if (i < size) {

                    EventSource source = enumerator.Value as EventSource;
                    buffer[i++] = source.SourceHandle;
                }
            }

            Lock.ReleaseMutex();
            return i;
        }

        public override int QueryEventTypeList(UIntPtr [] buffer, int size)
        {
            int i = 0;
            Lock.AcquireMutex();

            IDictionaryEnumerator enumerator = EventTable.GetEnumerator();
            while (enumerator.MoveNext()) {

                if (i < size) {

                    UIntPtr eventHandle = (UIntPtr)enumerator.Value;
                    buffer[i++] = eventHandle;
                }
            }

            Lock.ReleaseMutex();
            return i;
        }

        public override bool GetSourceInformation(UIntPtr sourceHandle,
                                                    ref UIntPtr storageHandle,
                                                    ref UIntPtr eventType,
                                                    ref UInt16 count,
                                                    ref string bufferName)
        {
            Lock.AcquireMutex();

            EventSource source = SourcesHandleTable[sourceHandle] as EventSource;

            if (source != null) {

                bufferName = source.SourceName;
                ActiveSource activeSource = source as ActiveSource;

                if (activeSource != null) {

                    storageHandle = 0;
                    eventType = activeSource.EventTypeHandle;
                    count = activeSource.Count;
                    
                } else {
                    storageHandle = source.Storage.GetHandle();
                    eventType = 0;
                    count = 0;
                }
                
                Lock.ReleaseMutex();

                return true;
            }
            
            Lock.ReleaseMutex();
            return false;
        }

        public override UIntPtr WalkEventDescriptor(UIntPtr eventHandle,
                                                    UIntPtr currentField,
                                                    ref UInt16 offset,
                                                    ref UInt16 type,
                                                    ref string bufferName)
        {
            UIntPtr fieldHandle = currentField;
            UInt16 tmpOffset;
            UInt16 tmpType;
            const UInt16 MaxBufferSize = 256;

            char[] tmpBufferName = new char[MaxBufferSize]; 

            unsafe {

                fixed(char* ptrBytes = &tmpBufferName[0]) {
                    
                    fieldHandle = MemoryStorage.WalkEventDescriptorImpl(eventHandle,
                                                                        fieldHandle,
                                                                        &tmpOffset,
                                                                        &tmpType,
                                                                        ptrBytes,
                                                                        MaxBufferSize);

                    if (fieldHandle != 0) {

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
            return fieldHandle;
        }

        public override bool QueryActiveEntry(UIntPtr sourceHandle,
                                             int index,
                                             ref QueryBuffer entryBuffer)
        {
            unsafe {

                UInt32 offset;
                UIntPtr type;
                
                fixed(byte * ptr = &(entryBuffer.GetBuffer()[0])) {

                    bool success = ReadActiveSourceItem(sourceHandle, index, &type, ptr, entryBuffer.GetBufferSize());


                    entryBuffer.Type = type;

                    // the active entries do not have any header

                    entryBuffer.UserOffset = 0;

                    return success;
                }
            }
        }

        public unsafe bool ReadActiveSourceItem(UIntPtr sourceHandle,
                                                        int item,
                                                        UIntPtr * type,
                                                        byte * buffer,
                                                        UInt16 bufferSize )
        {
            Lock.AcquireMutex();

            object source = SourcesHandleTable[sourceHandle];

            if (source != null) {
                ActiveSource activeSource =  source as ActiveSource;

                if (activeSource != null) {

                    bool success = activeSource.GetActiveEntry(item, type, buffer, bufferSize);
                    Lock.ReleaseMutex();

                    return success;
                }
            }
            
            Lock.ReleaseMutex();
            return false;
        }

        internal bool GetNativeSourceName(UIntPtr sourceHandle,
                                                   ref UIntPtr storageHandle,
                                                   ref string bufferName)
        {
            bool success = false;
            const UInt16 MaxBufferSize = 256;
            UIntPtr tmpHandle;

            char[] tmpBufferName = new char[MaxBufferSize]; 

            unsafe {

                fixed(char* ptrBytes = &tmpBufferName[0]) {

                    success = QueryNativeSourceInfo(sourceHandle, &tmpHandle, ptrBytes, MaxBufferSize);

                    if (success) {

                        string sourceName = "";

                        if (sourceName != null) {
                            for (int i = 0; i < MaxBufferSize; i++) {

                                if (tmpBufferName[i] == 0) {
                                    break;
                                }

                                sourceName += tmpBufferName[i];
                            }
                        }
                        bufferName = sourceName;
                        storageHandle = tmpHandle;
                    }
                }
            }
            return success;
        }

        // ABI interfaces

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe bool GetControllerHandle(UIntPtr * sourceHandle, UIntPtr * storageHandle);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr FetchLocalStorage();

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe bool SetRepositoryStorage(UIntPtr StorageHandle);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr RegisterEventDescriptorInternal(string eventName, 
                                                                            string eventDescription);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr RegisterEventFieldInternal(UIntPtr eventHandle,
                                                                       string fieldName,
                                                                       UInt16 offset,
                                                                       UInt16 type);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr RegisterEventGenericFieldInternal(UIntPtr eventHandle,
                                                                              string fieldName,
                                                                              UInt16 offset,
                                                                              UInt16 size,
                                                                              UIntPtr fieldTypeHandle);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr RegisterEnumDescriptorInternal(string enumName,
                                                                           UInt16 type);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr RegisterValueDescriptorInternal(UIntPtr enumHandle,
                                                                            string valueName,
                                                                            UInt64 value,
                                                                            byte flagChar);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe bool RegisterStorageImpl(UIntPtr StorageHandle);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe void UnRegisterStorageImpl(UIntPtr StorageHandle);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe UIntPtr AllocateSourceHandleImpl(string sourceName);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe void UnRegisterSourceImpl(UIntPtr sourceHandle);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe void RegisterSourceStorageImpl(UIntPtr sourceHandle, 
                                                                   UIntPtr storageHandle,
                                                                   UInt32 controlFlags);

        [AccessedByRuntime("output to header : defined in EventController.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe void RegisterActiveSourceImpl(UIntPtr sourceHandle, 
                                                                            UIntPtr eventTypeHandle,
                                                                            UIntPtr debuggerBufferAddress,
                                                                            UInt16 count,
                                                                            UInt16 entrySize);

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe bool QueryNativeSourceInfo(UIntPtr sourceHandle,
                                                               UIntPtr * storageHandle, 
                                                               char * bufferName,
                                                               UInt16 bufferSize );

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        public static extern unsafe int QuerySystemSources(UIntPtr * sourceHandles,
                                                           UInt16 arraySize );
    }    

    //
    //  Event source for controller entries. Events and traces related
    //  to the controller's activity will use this source for logging
    //  For now, then only interesting event logged is the creation of
    //  the controller, which is helpful to associate a process name and ID with the
    //  current controller
    //
    
    [CLSCompliant(false)]
    public class ControllerLogger : EventSource {

        public static ControllerLogger Create(string sourceName, EventingStorage storage) {

            ControllerLogger Logger  = new ControllerLogger(sourceName, 
                                                            storage,
                                                            CAPTURE_STACK_TRACE | ENABLE_ALL_MASK);

            if (Logger != null) {

                Logger.Register();
            }

            return Logger;
        }

        ControllerLogger(string sourceName, EventingStorage storage, uint controlFlags) 
            :base(sourceName, storage, controlFlags) {}
      
    }
}


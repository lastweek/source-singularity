////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EventQuery.cs
//
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
    // Delegates for the session and entry queries

    public class EnumerationContext
    {
        public EnumerationContext(){}
    }

    [CLSCompliant(false)]
    public delegate bool QuerySourceDelegate(UIntPtr sourceHandle,
                                             UIntPtr storageHandle,
                                             UIntPtr eventType,
                                             UInt16 count,
                                             string bufferName, 
                                             EventDescriptor Descriptor,
                                             ref EnumerationContext context);

    [CLSCompliant(false)]
    public delegate bool ActiveSourceEntryDelegate(UIntPtr sourceHandle,
                                                   int index,
                                                   EventDescriptor descriptor,
                                                   QueryBuffer entryBuffer,
                                                   ref EnumerationContext context);
    
    [CLSCompliant(false)]
    public delegate bool QueryEntryDelegate(EventDescriptor currentEntry, 
                                            QueryBuffer buffer, 
                                            ref EnumerationContext context);

    [CLSCompliant(false)]
    public delegate bool QueryFieldDelegate(FieldDescriptor fieldDescriptor, 
                                            object value, 
                                            ref EnumerationContext context);

    [CLSCompliant(false)]
    public class FieldDescriptor
    {
        public UInt16 Offset;
        public UInt16 Type;
        public string Name;

        public FieldDescriptor(UInt16 offset, UInt16 type, string name) 
        {
            Offset = offset;
            Type = type;
            Name = name;
        }

        public object GetObject(QueryBuffer buffer)
        {
            unsafe {

                switch (Type) {
                    case DataType.__int8:
                    case DataType.__uint8:
                        fixed(byte * ptrInt = &(buffer.GetBuffer()[buffer.UserOffset + Offset])) {

                            return *(byte *)ptrInt;
                        }

                    case DataType.__int16:
                    case DataType.__uint16:
                        fixed(byte * ptrInt = &(buffer.GetBuffer()[buffer.UserOffset + Offset])) {

                            return *(ushort *)ptrInt;
                        }

                    case DataType.__int32:
                    case DataType.__uint32:
                        fixed(byte * ptrInt = &(buffer.GetBuffer()[buffer.UserOffset + Offset])) {
                            return *(Int32 *)ptrInt;
                        }

                    case DataType.__UIntPtr:
                        fixed(byte * ptrInt = &(buffer.GetBuffer()[buffer.UserOffset + Offset])) {

                            return *(UIntPtr *)ptrInt;
                        }

                    case DataType.__IntPtr:
                        fixed(byte * ptrInt = &(buffer.GetBuffer()[buffer.UserOffset + Offset])) {

                            return *(IntPtr *)ptrInt;
                        }
                        
                    default:
                        DebugStub.WriteLine("Unknown field type");
                    break;
                }
            }

            return null;
        }

        public string GetTypeName() 
        {
            
            switch (Type) {
                case DataType.__int8: return "int8";
                case DataType.__int16: return "int16";
                case DataType.__int32: return "int32";
                case DataType.__int64: return "int64";
                case DataType.__uint8: return "uint8";
                case DataType.__uint16: return "uint16";
                case DataType.__uint32: return "uint32";
                case DataType.__uint64: return "uint64";
                case DataType.__IntPtr: return "IntPtr";
                case DataType.__UIntPtr: return "UIntPtr";
                case DataType.__arrayType:return "ArrayType";

                default:
                    return "unknown";
            }
        }

        
    }

    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in EventController.cpp")]
    public class EventDescriptor
    {
        internal UIntPtr EventHandle;
        internal string EventName;
        public ArrayList Fields;
        internal Hashtable LookupTable;
        internal Controller ControllerObject;

        public EventDescriptor(Controller controller, UIntPtr eventHandle)
        {
            EventHandle = eventHandle;
            ControllerObject = controller;
        }

        public string GetName()
        {
            return EventName;
        }

        public int GetFieldsCount()
        {
            return Fields.Count;
        }
        
        public bool Initialize()
        {
            UIntPtr fieldHandle = 0;
            UInt16 offset = 0;
            UInt16 type = 0;
            string fieldName = "";
            

            Fields = new ArrayList();
            LookupTable = new Hashtable();
            
            do {

                fieldHandle = ControllerObject.WalkEventDescriptor(EventHandle,
                                                                  fieldHandle,
                                                                  ref offset,
                                                                  ref type,
                                                                  ref fieldName);
                
                if (fieldHandle != 0) {

                    if (type == 0) {

                        // This entry describes the event metadata. Fetch the name here
                        
                        EventName = fieldName;
                        
                    } else {

                        // This is an actual field. Addit to our table
                        
                        FieldDescriptor fieldDescriptor = new FieldDescriptor(offset, 
                                                                              type, 
                                                                              fieldName);
                        if (fieldDescriptor == null) {
                            
                            return false;
                        }
                        
                        Fields.Add(fieldDescriptor);
                        LookupTable[fieldName] = fieldDescriptor;
                    }

                }
            } while (fieldHandle != 0);

            Fields.Reverse();

            return true;
            
        }

        public void EnumerateFields(QueryFieldDelegate fieldDelegate, 
                                    QueryBuffer buffer, 
                                    ref EnumerationContext context)
        {
            for (int i = 0; i < Fields.Count; i++) {

                FieldDescriptor fieldDescriptor = Fields[i] as FieldDescriptor;

                if (buffer != null) {
                    
                    if (!fieldDelegate(fieldDescriptor, fieldDescriptor.GetObject(buffer), ref context)) {

                        break;
                    }
                    
                } else {
                
                    if (!fieldDelegate(fieldDescriptor, null, ref context)) {

                        break;
                    }
                }
            }
        }
        
        public object GetProperty(QueryBuffer buffer, string propertyName)
        {
            FieldDescriptor fieldDescriptor = LookupTable[propertyName] as FieldDescriptor;

            if (fieldDescriptor == null) {
                
                return null;
            }

            return fieldDescriptor.GetObject(buffer);
        }
    }

    [CLSCompliant(false)]
    public class QueryBuffer
    {
        private byte [] Buffer = null;
        private UInt16 BufferSize;

        // offset of user-specific data in the buffer
        
        public UInt32 UserOffset;
        public UIntPtr Type;
        public UIntPtr EntryHandle;

        public QueryBuffer(UInt16 size)
        {
            BufferSize = size;
            Buffer = new byte[BufferSize];
        }

        [NoHeapAllocation]
        public byte[] GetBuffer()
        {
            return Buffer;
        }

        [NoHeapAllocation]
        public UInt16 GetBufferSize()
        {
            return BufferSize;
        }
    }

    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in EventController.cpp")]
    public class QuerySession
    {

        // Implementation details

        private QueryBuffer EntryBuffer;

        private EventingStorage QueryStorage = null;
        private UIntPtr QueryHandle = 0;

        public bool Initialize(EventingStorage storage, 
                               bool forward)
        {
            if (EntryBuffer == null) {
                
                EntryBuffer = new QueryBuffer(256);
                if ((EntryBuffer == null) || (EntryBuffer.GetBuffer() == null)) {

                    return false;
                }
            }

            //  Cleanup for the previous states.

            if (QueryHandle != 0) {
                
                QueryStorage.DeleteQueryView(QueryHandle);
                QueryHandle = 0;
                QueryStorage = null;
            }

            //  Initialize the new query states

            QueryStorage = storage;

            if (QueryStorage == null) {
                
                return false;
            }
            
            QueryHandle = QueryStorage.CreateQueryView(forward);
            
            if (QueryHandle == 0) {

                QueryStorage = null;
                
                return false;
            }

            return true;
        }

        public void EnumerateEntries(QueryEntryDelegate entryDelegate, 
                                     ref EnumerationContext context)
        {
            if ((QueryHandle != 0) && (entryDelegate!= null)) {
                
                UIntPtr entryHandle;
                
                do {
                    
                    entryHandle =  QueryStorage.GetNextEntry(QueryHandle , 
                                                             ref EntryBuffer);

                    if (entryHandle != 0) {

                        if (!entryDelegate(GetEventDescriptor(QueryStorage.GetController(),
                                                              EntryBuffer.Type), 
                                           EntryBuffer, 
                                           ref context)) {

                            break;
                        }
                    }

                } while (entryHandle != 0);

            }
            
        }

        //  General methods for event schema registration and lookup

        internal static Hashtable DescriptorTable = null;
        internal static Mutex Lock = null;
        internal static EventDescriptor EventMetadata = null;

        public static bool InitializeQuerySystem()
        {
            if (DescriptorTable != null) {

                return false;
            }
            
            DescriptorTable = new Hashtable();
            Lock = new Mutex();

            if ((Lock == null) || (DescriptorTable == null) ) {

                return false;
            }
            
            return true;
        }

        public static void FlushCaches()
        {
            Lock.AcquireMutex();
            DescriptorTable.Clear();
            Lock.ReleaseMutex();
        }

        public static EventDescriptor GetEventDescriptor(Controller controller, UIntPtr typeHandle)
        {
            Lock.AcquireMutex();
            EventDescriptor descriptor = DescriptorTable[typeHandle] as EventDescriptor;
            
            if (descriptor != null) {

                Lock.ReleaseMutex();
                return descriptor;
            }

            descriptor = new EventDescriptor(controller, typeHandle);
            
            if ((descriptor != null) && descriptor.Initialize()) {

                DescriptorTable[typeHandle] = descriptor;

                if (typeHandle == 0) {

                    EventMetadata = descriptor;
                }

            } else {

                descriptor = null;
            }

            Lock.ReleaseMutex();
            return descriptor;
        }
    }
}

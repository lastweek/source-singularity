////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EventType.cs
//
//  Note: Definition of the basic event types and classes
// 
//

using System;
using System.Threading;
using Microsoft.Singularity.Eventing;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Eventing
{

    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
    public class DataType {

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __int8 = 1;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __uint8 = 2;

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __int16 = 3;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __uint16 = 4;

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __int32 = 5;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __uint32 = 6;

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __int64 = 7;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __uint64 = 8;

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __IntPtr = 9;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __UIntPtr = 10;


        //  Other common aliases for existing basic data structures
        
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __byte = __uint8;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __int = __int32;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __uint = __uint32;

        //
        //  Bit array properties (higher bits of the type)
        //

        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __arrayType = 0x8000;
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __string = 0x4000; //  assume conversion to ascii at logging
        [AccessedByRuntime("output to header : defined in MemoryStorage.cpp")]
        public const ushort __szChar = 0x2000; 
    }
}

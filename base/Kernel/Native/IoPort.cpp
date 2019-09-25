////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoPort.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"

///////////////////////////////////////////////////////////// I/O Port Access.
//

// Note: eventually we need to fix the IoPort class for ARM.
// For now, though, we conditionalize this code since we don't have
// io port operations
//

uint8 Class_Microsoft_Singularity_Io_IoPort::g_HalReadInt8(uint32 port)
{
#if ISA_IX86 || ISA_IX64
    return __inbyte(port);
#else
    __debugbreak();
    return 0;
#endif
}

uint16 Class_Microsoft_Singularity_Io_IoPort::g_HalReadInt16(uint32 port)
{
#if ISA_IX86 || ISA_IX64
    return __inword(port);
#else
    __debugbreak();
    return 0;
#endif
}

uint32 Class_Microsoft_Singularity_Io_IoPort::g_HalReadInt32(uint32 port)
{
#if ISA_IX86 || ISA_IX64
    return __indword(port);
#else
    __debugbreak();
    return 0;
#endif
}

void Class_Microsoft_Singularity_Io_IoPort::g_HalWriteInt8(uint32 port,
                                                           uint8  value)
{
#if ISA_IX86 || ISA_IX64
    __outbyte(port, value);
#else
    __debugbreak();
#endif
}

void Class_Microsoft_Singularity_Io_IoPort::g_HalWriteInt16(uint32 port,
                                                            uint16 value)
{
#if ISA_IX86 || ISA_IX64
    __outword(port, value);
#else
    __debugbreak();
#endif
}

void Class_Microsoft_Singularity_Io_IoPort::g_HalWriteInt32(uint32 port,
                                                            uint32 value)
{
#if ISA_IX86 || ISA_IX64
    __outdword(port, value);
#else
    __debugbreak();
#endif
}

#if DO_UNSAFE_CODE_IN_IO

void Class_Microsoft_Singularity_Io_IoPort::g_HalReadFifo16(uint32 port,
                                                            uint16 *buffer,
                                                            uint32 count)
{
#if ISA_IX86 || ISA_IX64
    __inwordstring(port, buffer, count);
#else
    __debugbreak();
#endif
}

void Class_Microsoft_Singularity_Io_IoPort::g_HalWriteFifo16(uint32 port,
                                                             uint16 *buffer,
                                                             uint32 count)
{
#if ISA_IX86 || ISA_IX64
    __outwordstring(port, buffer, count);
#else
    __debugbreak();
#endif
}

#endif // DO_UNSAFE_CODE_IN_IO

//
///////////////////////////////////////////////////////////////// End of File.

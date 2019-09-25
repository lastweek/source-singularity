//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System.Runtime.CompilerServices;

namespace System.Runtime.CompilerServices
{
    // Method keeps interrupts disabled.
    // Note: [InterruptsDisabled] implies both [RequiresInterruptsDisabled]
    // and [EnsuresInterruptsDisabled].  Furthermore, [InterruptsDisabled]
    // is stronger than [RequiresInterruptsDisabled][EnsuresInterruptsDisabled],
    // since it keeps interrupts disabled until the method exits.
    class InterruptsDisabledAttribute: System.Attribute {}

    // Method requires interrupts disabled upon entry.
    class RequiresInterruptsDisabledAttribute: System.Attribute {}

    // Method ensures interrupts disabled upon exit.
    class EnsuresInterruptsDisabledAttribute: System.Attribute {}
}

class CompilerIntrinsics
{
    // These declarations are used by the (untrusted) C# compiler
    [Intrinsic]
    [EnsuresInterruptsDisabled]
    internal extern static void Cli();

    [Intrinsic]
    [RequiresInterruptsDisabled]
    internal extern static void Sti();
}

class NucleusCalls
{
    // These declarations are double-checked by the TAL checker
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static void Throw();

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static uint GetStackState(uint stackId);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static void ResetStack(uint stackId);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    internal extern static void YieldTo(uint stackId);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static void GarbageCollect();

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static void VgaTextWrite(uint position, uint data);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static uint TryReadKeyboard();

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static void StartTimer(uint freq);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static void SendEoi();

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static byte[] PciDmaBuffer();

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static uint PciDmaPhysicalAddr();

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static uint PciConfigRead32(uint id, uint offset);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    // Establishes PCI memory region.  Returns size of memory region.
    internal extern static uint PciMemSetup(uint id);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static uint PciMemRead32(uint id, uint offset);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static void PciMemWrite32(uint id, uint offset, uint val);

    // TODO: this can be a compiler intrinsic
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static long Rdtsc();

    // TODO: this can be a C# method
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
    [InterruptsDisabled]
    internal extern static void DebugPrintHex(uint screenOffset, uint hexMessage);
}

class INucleusCalls
{
    [RequiredByBartok]
    internal static void Throw()
    {
        CompilerIntrinsics.Cli();
        NucleusCalls.Throw();
        while(true) {}
    }

    internal static void VgaTextWrite(uint position, uint data)
    {
        try
        {
            CompilerIntrinsics.Cli();
            NucleusCalls.VgaTextWrite(position, data);
        }
        finally
        {
            CompilerIntrinsics.Sti();
        }
    }

    internal static uint TryReadKeyboard()
    {
        try
        {
            CompilerIntrinsics.Cli();
            return NucleusCalls.TryReadKeyboard();
        }
        finally
        {
            CompilerIntrinsics.Sti();
        }
    }

    internal static long Rdtsc()
    {
        try
        {
            CompilerIntrinsics.Cli();
            return NucleusCalls.Rdtsc();
        }
        finally
        {
            CompilerIntrinsics.Sti();
        }
    }

    internal static void DebugPrintHex(uint screenOffset, uint hexMessage)
    {
        try
        {
            CompilerIntrinsics.Cli();
            NucleusCalls.DebugPrintHex(screenOffset, hexMessage);
        }
        finally
        {
            CompilerIntrinsics.Sti();
        }
    }
}


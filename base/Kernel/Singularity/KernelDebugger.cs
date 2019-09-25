////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.KernelDebugger
{
    /// <summary>
    /// This class exposes some of the unmanaged kernel debugger functions, mainly
    /// KdSendPacket and KdReceivePacket.  Eventually, more of the kernel debugger
    /// support should be moved out of halkd.cpp and into this class.
    /// 
    /// The main consumer of this class is the KdFiles class.
    /// </summary>
    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : methods defined in halkd.cpp")]
    public class Kd
    {
        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        public static unsafe extern void SendPacket(
            uint PacketType,
            byte* MessageHeaderBuffer,
            int MessageHeaderLength,
            byte* MessageDataBuffer,
            int MessageDataLength
            );

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        public static unsafe extern /*KdStatus*/ uint ReceivePacket(
            uint PacketType,
            byte* MessageHeaderBuffer,
            int MessageHeaderLength,
            byte* MessageDataBuffer,
            int MessageDataBufferLength,
            out int MessageDataLength
            );

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        public static extern void Lock();

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        public static extern void Unlock();

        public static unsafe void SendPacket(
            KdPacketType PacketType,
            byte* MessageHeaderBuffer,
            int MessageHeaderLength,
            byte* MessageDataBuffer,
            int MessageDataLength
            )
        {
            // DebugStub.WriteLine(String.Format("MessageHeaderBuffer = 0x{0:x}", (UIntPtr)MessageHeaderBuffer));
            // DebugStub.WriteLine("Kd.SendPacket: Sending packet to KD...");
            // Console.WriteLine("Kd.SendPacket: Sending packet to KD...");
            SendPacket(
                (uint)PacketType,
                MessageHeaderBuffer,
                MessageHeaderLength,
                MessageDataBuffer,
                MessageDataLength);
            // DebugStub.WriteLine("Kd.SendPacket: KdSendPacket has returned.");
            // Console.WriteLine("Kd.SendPacket: KdSendPacket has returned.");
        }

        public static unsafe KdStatus ReceivePacket(
            KdPacketType PacketType,
            byte* MessageHeaderBuffer,
            int MessageHeaderLength,
            byte* MessageDataBuffer,
            int MessageDataBufferLength,
            out int MessageDataLength
            )
        {
            // DebugStub.WriteLine(String.Format("Kd.ReceivePacket: MessageHeaderBuffer = 0x{0:x}", (UIntPtr)MessageHeaderBuffer));
            // Console.WriteLine("Kd.ReceivePacket: Waiting for packet from KD...");

            KdStatus status = (KdStatus)ReceivePacket(
                (uint)PacketType,
                MessageHeaderBuffer,
                MessageHeaderLength,
                MessageDataBuffer,
                MessageDataBufferLength,
                out MessageDataLength);

            // Console.WriteLine("Kd.ReceivePacket: KdReceivePacket has returned.  Status = " + status);
            // DebugStub.Break();
            return status;
        }

        public static unsafe bool SendRequestWaitResponse(
            KdPacketType PacketType,
            byte* RequestHeaderBuffer,
            int RequestHeaderLength,
            byte* RequestDataBuffer,
            int RequestDataLength,
            byte* ResponseHeaderBuffer,
            int ResponseHeaderLength,
            byte* ResponseDataBuffer,
            int ResponseDataMaximumLength,
            out int ResponseDataActualLength)
        {
            ResponseDataActualLength = 0;

        send_packet:
            if (!IsDebuggerPresent())
                return false;

            SendPacket(
                PacketType,
                RequestHeaderBuffer,
                RequestHeaderLength,
                RequestDataBuffer,
                RequestDataLength);

        receive_packet:
            KdStatus status = (KdStatus)ReceivePacket(
                (uint)PacketType,
                ResponseHeaderBuffer,
                ResponseHeaderLength,
                ResponseDataBuffer,
                ResponseDataMaximumLength,
                out ResponseDataActualLength);

            if (status == KdStatus.PacketReceived) {
                Dbg("Received response.  Actual data length = {0}", ResponseDataActualLength);
                return true;
            }

            if (status == KdStatus.PacketTimeout) {
                if (IsDebuggerPresent()) {
                    Dbg("Received PacketTimeout, trying again");
                    goto receive_packet;
                }
                else {
                    ResponseDataActualLength = 0;
                    return false;
                }
            }

            if (status == KdStatus.PacketResend) {
                Dbg("Received PacketResend -- resending packet.");
                goto send_packet;
            }

            Dbg("Received unrecognized response from KdReceivePacket.  Return value: {0}", (uint)status);
            ResponseDataActualLength = 0;
            return false;
        }

        public static bool IsDebuggerPresent()
        {
            return DebugStub.IsDebuggerPresent();
        }

        public const int MaxPacketSize = 4096;

        static bool _debug_to_console;

        static void Dbg(string line)
        {
            if (_debug_to_console)
                Console.WriteLine("KernelDebugger.cs: " + line);
        }

        static void Dbg(string format, params object[] args)
        {
            Dbg(String.Format(format, args));
        }
    }

    /// <summary>
    /// Compatible with PACKET_TYPE_XXX defines in halkd.h.
    /// </summary>
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from halkd.cpp")]
    public enum KdPacketType : uint
    {
        Unused                          = 0,
        StateChange32                   = 1,
        StateManipulate                 = 2,
        DebugIo                         = 3,
        Acknowledge                     = 4,// Packet-control type
        Resend                          = 5,// Packet-control type
        Reset                           = 6,// Packet-control type
        StateChange64                   = 7,
        PollBreakin                     = 8,
        TraceIo                         = 9,
        ControlRequest                  = 10,
        [AccessedByRuntime("referenced from halkd.cpp")] FileIo = 11,
        MaxValue                        = 12,
    }

    /// <summary>
    /// These values identify the structure of messages / requests sent between 
    /// the kernel and KD.  Compatible with DbgKdXxxApi values.
    /// </summary>
    [CLSCompliant(false)]
    public enum KdApi : uint
    {
        // State change constants
        MinimumStateChange              = 0x00003030u,
        ExceptionStateChange            = 0x00003030u,
        LoadSymbolsStateChange          = 0x00003031u,
        CommandStringStateChange        = 0x00003032u,
        MaximumStateChange              = 0x00003033u,

        //
        // If the packet type is PACKET_TYPE_KD_STATE_MANIPULATE, then
        // the format of the packet data is as follows:
        //
        // Api Numbers for state manipulation
        //

        MinimumManipulate               = 0x00003130u,

        ReadVirtualMemoryApi            = 0x00003130u,
        WriteVirtualMemoryApi           = 0x00003131u,
        GetContextApi                   = 0x00003132u,
        SetContextApi                   = 0x00003133u,
        WriteBreakPointApi              = 0x00003134u,
        RestoreBreakPointApi            = 0x00003135u,
        ContinueApi                     = 0x00003136u,
        ReadControlSpaceApi             = 0x00003137u,
        WriteControlSpaceApi            = 0x00003138u,
        ReadIoSpaceApi                  = 0x00003139u,
        WriteIoSpaceApi                 = 0x0000313Au,
        RebootApi                       = 0x0000313Bu,
        ContinueApi2                    = 0x0000313Cu,
        ReadPhysicalMemoryApi           = 0x0000313Du,
        WritePhysicalMemoryApi          = 0x0000313Eu,
        //QuerySpecialCallsApi          = 0x0000313FL
        SetSpecialCallApi               = 0x00003140u,
        ClearSpecialCallsApi            = 0x00003141u,
        SetInternalBreakPointApi        = 0x00003142u,
        GetInternalBreakPointApi        = 0x00003143u,
        ReadIoSpaceExtendedApi          = 0x00003144u,
        WriteIoSpaceExtendedApi         = 0x00003145u,
        GetVersionApi                   = 0x00003146u,
        WriteBreakPointExApi            = 0x00003147u,
        RestoreBreakPointExApi          = 0x00003148u,
        CauseBugCheckApi                = 0x00003149u,
        SwitchProcessor                 = 0x00003150u,
        PageInApi                       = 0x00003151u,// obsolete
        ReadMachineSpecificRegister     = 0x00003152u,
        WriteMachineSpecificRegister    = 0x00003153u,
        OldVlm1                         = 0x00003154u,
        OldVlm2                         = 0x00003155u,
        SearchMemoryApi                 = 0x00003156u,
        GetBusDataApi                   = 0x00003157u,
        SetBusDataApi                   = 0x00003158u,
        CheckLowMemoryApi               = 0x00003159u,
        ClearAllInternalBreakpointsApi  = 0x0000315Au,
        FillMemoryApi                   = 0x0000315Bu,
        QueryMemoryApi                  = 0x0000315Cu,
        SwitchPartition                 = 0x0000315Du,

        MaximumManipulate               = 0x0000315Eu,


        //
        // If the packet type is PACKET_TYPE_KD_FILE_IO, then
        // the format of the packet data is as follows:
        //

        CreateFile                      = 0x00003430u,
        ReadFile                        = 0x00003431u,
        WriteFile                       = 0x00003432u,
        CloseFile                       = 0x00003433u,
    }


    /// <summary>
    /// Declares error codes for Kd.ReceivePacket.  Values are compatible
    /// with unmanaged defines KDP_PACKET_RECEIVED, etc.
    /// </summary>
    [AccessedByRuntime("referenced from halkd.cpp")]
    public enum KdStatus
    {
        [AccessedByRuntime("referenced from halkd.cpp")]
        PacketReceived = 0,

        [AccessedByRuntime("referenced from halkd.cpp")]
        PacketTimeout = 1,

        [AccessedByRuntime("referenced from halkd.cpp")]
        PacketResend = 2,

    }
}



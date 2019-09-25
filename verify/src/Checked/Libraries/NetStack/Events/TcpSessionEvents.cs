// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Runtime.CompilerServices;

//using Microsoft.Singularity.Transform;
//using Microsoft.Singularity.Eventing;

namespace Microsoft.Singularity.NetStack.Events
{
    /// <summary>
    /// TCP Contract Entrypoints (use enums, not strings, for density).
    /// </summary>
    public enum TcpSessionContractEntrypoints : byte
    {
        Unknown = 0,

        Connect,
        Bind,
        Listen,
        Accept,
        DoneSending,
        DoneReceiving,
        Abort,
        Close,
        BindLocalEndPoint,

        Read,
        PollRead,
        Write,

        IsSessionAvailable,
        IsDataAvailable,

        GetLocalAddress,
        GetLocalPort,
        GetRemoteAddress,
        GetRemotePort,

        ChannelClosed,
    }

    /// <summary>
    /// Event Definitions for the TcpSession class.
    /// </summary>
    //[Event]
    public abstract class TcpSessionEvents : EventSource
    {
        //[EventEnum]
        public enum TcpSessionState : byte
        {
            Unknown = 0,
            Closed = 1,
            Listen = 2,
            SynRecvd = 3,
            SynSent = 4,
            Established = 5,
            CloseWait = 6,
            LastAck = 7,
            FinWait1 = 8,
            FinWait2 = 9,
            Closing = 10,
        };

        internal static readonly string[] TcpSessionStateNames = new string[] {
            "Undefined",
            "Closed   ",
            "Listen   ",
            "SynRecvd ",
            "SynSent  ",
            "Establish",
            "CloseWait",
            "LastAck  ",
            "FinWait1 ",
            "FinWait2 ",
            "Closing  ",
        };
        
        public static TcpSessionEvents EventLog;

        //[Event]
        public abstract bool TcpSessionStateChangeEvent(
            ushort sessionId,
            TcpSessionState fromState,
            TcpSessionState toState);
        public static string TcpSessionStateChangeEvent_Format = "TCP: Ses{0,3} ({1}) State Change to {2}.";

        public static UIntPtr TcpSessionState_Handle;

        //[EventEnum]
        public enum TcpPacketFlags
        {
            F = 1 << 0,
            S = 1 << 1,
            R = 1 << 2,
            P = 1 << 3,
            A = 1 << 4,
            I = 1 << 5,
            E = 1 << 6,
            C = 1 << 7,
        };
        
        internal static readonly string[] TcpPacketFlagsNames = new string[] {
            "F", "S", "R", "P", "A", "I", "E", "C",
        };

        //[Event]
        public abstract bool TcpSessionReceivedPacketEvent(
            ushort sessionId,
            TcpSessionState currentState,
            TcpPacketFlags packetFlags,
            uint packetLength);
        public static string TcpSessionReceivedPacketEvent_Format = "TCP: Ses{0,3} ({1}) Packet ({2}) Len{3,4} received";

        public static UIntPtr TcpPacketFlags_Handle;

/*
        public override void RegisterEnumSymbols()
        {
            base.RegisterEnumSymbols();

            // Register the Tcp Session State enumeration (values, not flags).
            if (HostController.RegisterEnum("TcpSessionState",
                                            DataType.__uint8,
                                            ref TcpSessionState_Handle))
            {
                for (int enumValue = 0;
                         enumValue < TcpSessionStateNames.Length;
                         enumValue++)
                {
                    HostController.RegisterEnumValue(TcpSessionState_Handle,
                                                     TcpSessionStateNames[enumValue],
                                                     (UInt64)enumValue,
                                                     0);
                }
            }

            // Register the Tcp Packet Flags enumeration (flags, not values).
            if (HostController.RegisterEnum("TcpPacketFlags",
                                            DataType.__uint8,
                                            ref TcpPacketFlags_Handle))
            {
                for (int shift = 0; shift < 8; ++shift)
                {
                    HostController.RegisterEnumValue(TcpPacketFlags_Handle,
                                                     TcpPacketFlagsNames[shift],
                                                     1ul << shift,
                                                     (byte)TcpPacketFlagsNames[shift][0]);
                }
            }
        }
*/
    }
}

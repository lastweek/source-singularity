// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
// author: Glenn Peterson
// 

using System;
using System.Runtime.CompilerServices;
using System.Text;

#if !SINGULARITY
using System.Net;
#endif

using Microsoft.Contracts;
using Microsoft.Singularity;
using Microsoft.Singularity.Eventing;

using Microsoft.Singularity.NetStack.Events;

namespace NetStack.Runtime
{
    /// <summary>
    /// A class-only attribute to denote an Event Logging Source.
    /// </summary>
    [AttributeUsage(AttributeTargets.Class)]
    public sealed class EventLogSourceAttribute : Attribute
    {
        private string id = String.Empty;
        private bool fieldRegistrationErrorFatal = true;

        /// <summary>
        /// Sole constructor requiring the source Identifier as the only parameter.
        /// </summary>
        /// <params name="id">
        /// A string identifier for the particular event logging <b>source</b>.
        /// </params>
        public EventLogSourceAttribute(string id)
        {
            this.id = id;
        }

        /// <summary>
        /// A string identifier for the particular event logging <b>source</b>.
        /// </summary>
        public string Id
        {
            get { return this.id; }
            set { this.id = value; }
        }

        /// <summary>
        /// A Boolean that dictates the handling of a field registration errors.
        /// If <b>true</b> (the default), any field registration error causes
        /// the entire registration, and therefore the Create method, to fail.
        /// </summary>
        public bool FieldRegistationErrorFatal
        {
            get { return this.fieldRegistrationErrorFatal; }
            set { this.fieldRegistrationErrorFatal = value; }
        }
    }

    /// <summary>
    /// A method-only attribute denoting an Event Logging Method.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class EventLogMethodAttribute : System.Attribute
    {
        private string id;
        private bool heapAllowed = true;
        private bool debugPrint = false;
        private string formatString = String.Empty;

        /// <summary>
        /// Sole constructor requiring the method (event type)
        /// identifier as the only parameter.
        /// </summary>
        /// <params name="id">
        /// A string identifier for the particular event logging <b>method</b>
        /// which becomes the identifier for the event type.
        /// </params>
        public EventLogMethodAttribute(string id)
        {
            this.id = id;
        }

        /// <summary>
        /// A string identifier for the particular event logging <b>method</b>
        /// which becomes the identifier for the event type.
        /// </summary>
        public string Id
        {
            get { return this.id; }
            set { this.id = value; }
        }

        /// <summary>
        /// If true, the generated code can perform heap allocations.  NOT SURE IF NEEDED.  // TODO
        /// </summary>
        public bool HeapAllowed
        {
            get { return this.heapAllowed; }
            set { this.heapAllowed = value; }
        }

        /// <summary>
        /// If true, the generated code will include a test
        /// for the DebugPrint bit for this event type.
        /// </summary>
        public bool DebugPrint
        {
            get { return this.debugPrint; }
            set { this.debugPrint = value; }
        }

        /// <summary>
        /// A 'String.Format' format control string used when:
        /// <para>
        /// 1. The event is transferred to the debugger, and
        /// </para>
        /// <para>
        /// 2. The event is displayed with the script tool in a mixed stream.
        /// </para>
        /// </summary>
        public string FormatString
        {
            get { return this.formatString; }
            set { this.formatString = value; }
        }
    }

    /// <summary>
    /// A parameter-only attribute describing the treatment
    /// of a single parameter to an event logging method.
    /// </summary>
    /// <remarks>
    /// No Id is present as a Property as the parameter's
    /// name is the natural Id.
    /// </remarks>
    [AttributeUsage(AttributeTargets.Parameter)]
    public sealed class EventLogMethodParameterAttribute : Attribute
    {
        private string title = String.Empty;
        private uint ordinalInStruct;
        private string typeInStruct = String.Empty;

        /// <summary>
        /// A string used in lieu of the parameter name in columnar reports.
        /// </summary>
        /// <remarks>If not supplied, the parameter name is used.</remarks>
        public string Title
        {
            get { return this.title; }
            set { this.title = value; }
        }

        /// <summary>
        /// Specifies the zero-based ordinal of this parameter in the structure
        /// used to add this event to the event stream.
        /// </summary>
        /// <remarks>
        /// If not supplied, the parameter order in the method call is used.
        /// </remarks>
        public uint OrdinalInStruct
        {
            get { return this.ordinalInStruct; }
            set { this.ordinalInStruct = value; }
        }

        /// <summary>
        /// Specifies the type of the data element to use in the structure used
        /// to add this event to the event stream.
        /// </summary>
        /// <remarks>
        /// If not supplied, the type of the parameter in the method call is used.
        /// </remarks>
        public string TypeInStruct  // BUGBUG: Should not be a string, should be a value-type.  // TODO
        {
            get { return this.typeInStruct; }
            set { this.typeInStruct = value; }
        }
    }

    /// <summary>
    /// Eventing and Tracing support for the TcpSession class.
    /// </summary>
    [CLSCompliant(false)]
    [EventLogSource("TcpSession")]
    public class TcpSessionEventsSource : EventSource // TODO: Base class constructor should take storageOptions and Size - then the static almost goes away.
    {
        public const uint LogStateChanges              = 0x00010000;
        public const uint LogReceivedPackets           = 0x00020000;
        public const uint LogSendingPackets            = 0x00040000;
        public const uint LogTimeouts                  = 0x00080000;

        public const uint LogStateChangeContractCalls  = 0x00100000;
        public const uint LogDataTransferContractCalls = 0x00200000;
        public const uint LogQueryContractCalls        = 0x00400000;
        public const uint LogInfoContractCalls         = 0x00800000;

        // Event Log size in bytes.
        //  Overhead is 24 bytes and TcpSession uses <= 8.
        private const uint EventLogBufferSize = 32u * 2048u;

        // Global Instance
        public static readonly TcpSessionEventsSource EventLog;

        // Enums to represent TCP Contract Entrypoints
        public enum TcpSessionContractEntrypoints
        {
            Unknown = 0,

            Connect, Bind, Listen, Accept,
            DoneSending, DoneReceiving, Abort, Close,
            BindLocalEndPoint,

            Read, PollRead, Write,

            IsSessionAvailable, IsDataAvailable,

            GetLocalAddress, GetLocalPort,
            GetRemoteAddress, GetRemotePort,

            ChannelClosed,
        }

        // Strings matching enum immediately above.
        internal static readonly string[] ContractCallNames = new string[]
        {
            "Unknown",

            "Connect", "Bind", "Listen", "Accept",
            "DoneSending", "DoneReceiving", "Abort", "Close",
            "BindLocalEndPoint",

            "Read", "PollRead", "Write",

            "IsSessionAvailable", "IsDataAvailable",

            "GetLocalAddress", "GetLocalPort",
            "GetRemoteAddress", "GetRemotePort",

            "ChannelClosed",
        };

        private UIntPtr stateChangeTypeHandle;
        private UIntPtr receivedPacketTypeHandle;
        private UIntPtr sendingPacketTypeHandle;
        private UIntPtr timeoutTypeHandle;

        private UIntPtr contractCallTypeHandle;

        private uint debugOptions;

        private struct StateChangeEntry
        {
            public ushort sessionId;
            public byte fromState;
            public byte toState;

            public StateChangeEntry(uint sessionId, TcpStateEnum fromState, TcpStateEnum toState)
            {
                this.sessionId = (ushort)sessionId;
                this.fromState = (byte)fromState;
                this.toState = (byte)toState;
            }
        }

        private struct ReceivedPacketEntry
        {
            public ushort sessionId;
            public byte sessionState;
            public byte packetFlags;
            public ushort packetLength;

            public ReceivedPacketEntry(uint sessionId, TcpStateEnum sessionState, uint packetFlags, uint packetLength)
            {
                this.sessionId = (ushort)sessionId;
                this.sessionState = (byte)sessionState;
                this.packetFlags = (byte)packetFlags;
                this.packetLength = (ushort)packetLength;
            }
        }

        private struct SendingPacketEntry
        {
            public ushort sessionId;
            public byte sessionState;
            public byte packetFlags;
            public ushort packetLength;

            public SendingPacketEntry(uint sessionId, TcpStateEnum sessionState, uint packetFlags, uint packetLength)
            {
                this.sessionId = (ushort)sessionId;
                this.sessionState = (byte)sessionState;
                this.packetFlags = (byte)packetFlags;
                this.packetLength = (ushort)packetLength;
            }
        }

        private struct TimeoutEntry
        {
            public ushort sessionId;
            public byte sessionState;
            public byte timeoutType;

            public TimeoutEntry(uint sessionId, TcpStateEnum sessionState, TcpSession.TcpTimeoutType timeoutType)
            {
                this.sessionId = (ushort)sessionId;
                this.sessionState = (byte)sessionState;
                this.timeoutType = (byte)timeoutType;
            }
        }

        private struct ContractCallEntry
        {
            public ushort sessionId;
            public byte sessionState;
            public byte callId;

            public ContractCallEntry(uint sessionId, TcpStateEnum sessionState,
                                     TcpSessionContractEntrypoints callId)
            {
                this.sessionId = (ushort)sessionId;
                this.sessionState = (byte)sessionState;
                this.callId = (byte)callId;
            }
        }

        /// <summary>
        /// The Static Constructor.  It creates the event session for this SIP.
        /// </summary>
        static TcpSessionEventsSource()
        {
            TcpSessionEventsSource.EventLog = TcpSessionEventsSource.Create(// BUGBUG AM: Why isn't this a normal constructor????
                "TcpSessions",
                TcpSessionEventsSource.EventLogBufferSize,
                QualityOfService.RecyclableEvents,
                EventSource.ENABLE_ALL_MASK & ~(       // Buffering Mask   // BUGBUG: Switch to Positive Logic when system and user masks separated?  // TODO
                //Incl  TcpSessionEventsSource.LogStateChanges |
                /*Omit*/TcpSessionEventsSource.LogSendingPackets |
                //Incl  TcpSessionEventsSource.LogReceivedPackets |
                //Incl  TcpSessionEventsSource.LogTimeouts |
                //Incl  TcpSessionEventsSource.LogStateChangeContractCalls |
                /*Omit*/TcpSessionEventsSource.LogDataTransferContractCalls |
                /*Omit*/TcpSessionEventsSource.LogQueryContractCalls |
                /*Omit*/TcpSessionEventsSource.LogInfoContractCalls |
                        0u),
                EventSource.ENABLE_ALL_MASK & ~(       // Debugging Mask   // BUGBUG: Same // TODO
                /*Omit*/TcpSessionEventsSource.LogStateChanges |
                /*Omit*/TcpSessionEventsSource.LogSendingPackets |
                /*Omit*/TcpSessionEventsSource.LogReceivedPackets |
                /*Omit*/TcpSessionEventsSource.LogTimeouts |
                /*Omit*/TcpSessionEventsSource.LogStateChangeContractCalls |
                /*Omit*/TcpSessionEventsSource.LogDataTransferContractCalls |
                /*Omit*/TcpSessionEventsSource.LogQueryContractCalls |
                /*Omit*/TcpSessionEventsSource.LogInfoContractCalls |
                        0u));

#if false
            TcpSessionEvents.EventLog =
                TcpSessionEvents.Create("TcpSession",
                                        4096,
                                        QualityOfService.RecyclableEvents,
                                        EventSource.ENABLE_ALL_MASK |
                                        EventSource.CAPTURE_DEBUG_PRINT);
#endif
        }

        /// <summary>
        /// Create and Register a TcpSessionEventsSource.
        /// </summary>
        /// <devdoc>
        /// This should be a Generic when supported.  Or use more of the base class (Static?)  // BUGBUG AM (later?)
        /// </devdoc>
        public static TcpSessionEventsSource Create(string sourceName,
                                                    uint size,
                                                    uint storageOptions,   // BUGBUG AM: [Flags] enum
                                                    uint sourceFlags,
                                                    uint debugFlags)
        {
            TcpSessionEventsSource tcpSessionEventsSource = null;

            EventingStorage eventStorage =
                EventingStorage.CreateLocalStorage(storageOptions, size);
            if (eventStorage == null)
            {
                DebugStub.WriteLine("Failure to obtain storage for TcpSessionEvents");
                DebugStub.Break();
            }
            else
            {
                tcpSessionEventsSource =
                    new TcpSessionEventsSource(sourceName, eventStorage, sourceFlags, debugFlags);
                if (tcpSessionEventsSource == null)
                {
                    // TODO: Is EventStorage returned here and below if failures occur?
                    DebugStub.WriteLine("Failure to construct TcpSessionEventsSource instance.");
                    DebugStub.Break();
                }
                else
                {
                    bool registerSucceeded = tcpSessionEventsSource.Register();
                    if (registerSucceeded == false)
                    {
                        tcpSessionEventsSource = null;
                        DebugStub.WriteLine("Failure to register TcpSessionEventsSource.");
                        DebugStub.Break();
                    }
                }
            }

            return tcpSessionEventsSource;
        }

        /// <summary>Fully parameterized and sole constructor.</summary>
        /// <devdoc>BUGBUG AM: parameterization: have base EP that takes storageoptions and size to elim dup code (generated or not)</devdoc>
        public TcpSessionEventsSource(string sourceName, EventingStorage storage, uint controlFlags, uint debugOptions)
            : base(sourceName, storage, controlFlags)
        {
            this.debugOptions = debugOptions;
        }

        ~TcpSessionEventsSource()
        {
            // BUGBUG AM: Free EventingStorage (using base somehow?  please!)
        }

        //[NoHeapAllocation]
        [EventLogMethod("TcpSessionStateChange",
                         HeapAllowed = true,
                         DebugPrint = false,
                         FormatString = "TCP: Ses{0,3} ({1}) State Change to {2}.")]
        public bool LogSessionStateChange(
            [EventLogMethodParameter(Title = "Session", OrdinalInStruct = 0, TypeInStruct = "ushort")]
            uint sessionId,
            [EventLogMethodParameter(Title = "FrState", OrdinalInStruct = 1, TypeInStruct = "byte")]
            TcpStateEnum fromState,
            [EventLogMethodParameter(Title = "ToState", OrdinalInStruct = 2, TypeInStruct = "byte")]
            TcpStateEnum toState)   // BUGBUG AM: signature poor way to differentiate various entries.  Is there a way to have two two "int" loggers with different types and member labels?
        {
            if ((debugOptions & LogStateChanges /* To Debugger */) != 0)
            {
                Core.Log("TCP: Ses{0,3} ({1}) State Change to {2}.",
                         sessionId,
                         TcpState.TcpStateNames[(uint)fromState],
                         TcpState.TcpStateNames[(uint)toState]);
            }

            if ((ControlFlags & LogStateChanges) != 0)
            {
                StateChangeEntry stateChangeEntry =
                    new StateChangeEntry(sessionId, fromState, toState);

                unsafe
                {            // BUGBUG AM: Just a comment - this causes my otherwise safe compile to be changed to unsafe.  This is bad.
                    return (LogEntry(ControlFlags,
                                     stateChangeTypeHandle,
                                     (byte*)&stateChangeEntry,
                                     sizeof(StateChangeEntry)) != 0);
                }
            }

            return false;
        }

        //[NoHeapAllocation]
        [EventLogMethod("TcpPacketReceived",
                         HeapAllowed = true,
                         DebugPrint = false,
                         FormatString = "TCP: Ses{0,3} ({1}) Packet ({2}) Len{3,4} received")]
        public bool LogReceivedPacket(
            [EventLogMethodParameter(Title = "Session Id", OrdinalInStruct = 0, TypeInStruct = "ushort")]
            uint sessionId,
            [EventLogMethodParameter(Title = "Session State", OrdinalInStruct = 1, TypeInStruct = "byte")]
            TcpStateEnum sessionState,
            [EventLogMethodParameter(Title = "Packet Flags", OrdinalInStruct = 2, TypeInStruct = "byte")]
            uint packetFlags,
            [EventLogMethodParameter(Title = "Packet Length", OrdinalInStruct = 3, TypeInStruct = "ushort")]
            uint packetLength)
        {
            if ((debugOptions & LogReceivedPackets /* To Debugger */) != 0)
            {
                string flagsText = FlagsToText(packetFlags);    // TODO Move then Qualify
                Core.Log("TCP: Ses{0,3} ({1}) Packet ({2}) Len{3,4} received",
                         sessionId,
                         TcpState.TcpStateNames[(uint)sessionState],
                         flagsText,
                         packetLength);
            }

            if ((ControlFlags & LogReceivedPackets) != 0)
            {
                ReceivedPacketEntry receivedPacketEntry =
                    new ReceivedPacketEntry(sessionId, sessionState, packetFlags, packetLength);

                unsafe
                {
                    return (LogEntry(ControlFlags,
                                     receivedPacketTypeHandle,
                                     (byte*)&receivedPacketEntry,
                                     sizeof(ReceivedPacketEntry)) != 0);
                }
            }

            return false;
        }

        //[NoHeapAllocation]
        [EventLogMethod("TcpPacketSending",
                         HeapAllowed = true,
                         DebugPrint = false,
                         FormatString = "TCP: Ses{0,3} ({1}) Packet ({2}) Len{3,4} being sent")]
        public bool LogSendingPacket(
            [EventLogMethodParameter(Title = "Session Id",    OrdinalInStruct = 0, TypeInStruct = "ushort")]
            uint sessionId,
            [EventLogMethodParameter(Title = "Session State", OrdinalInStruct = 1, TypeInStruct = "byte")]
            TcpStateEnum sessionState,
            [EventLogMethodParameter(Title = "Packet Flags",  OrdinalInStruct = 2, TypeInStruct = "byte")]
            uint packetFlags,
            [EventLogMethodParameter(Title = "Packet Length", OrdinalInStruct = 3, TypeInStruct = "ushort")]
            uint packetLength)
        {
            if ((debugOptions & LogSendingPackets /* To Debugger */) != 0)
            {
                string flagsText = FlagsToText(packetFlags);    // TODO Move then Qualify
                Core.Log("TCP: Ses{0,3} ({1}) Packet ({2}) Len{3,4} being sent",
                         sessionId,
                         TcpState.TcpStateNames[(uint)sessionState],
                         flagsText,
                         packetLength);
            }

            if ((ControlFlags & LogSendingPackets) != 0)
            {
                SendingPacketEntry sendingPacketEntry =
                    new SendingPacketEntry(sessionId, sessionState, packetFlags, packetLength);

                unsafe
                {
                    return (LogEntry(ControlFlags,
                                     sendingPacketTypeHandle,
                                     (byte*)&sendingPacketEntry,
                                     sizeof(SendingPacketEntry)) != 0);
                }
            }

            return false;
        }

        //[NoHeapAllocation]
        [EventLogMethod("TcpTimeout",
                         HeapAllowed = true,
                         DebugPrint = false,
                         FormatString = "TCP: Ses{0,3} ({1}) Timeout of type '{2}' occurred")]
        public bool LogTimeout(
            [EventLogMethodParameter(Title = "Session Id", OrdinalInStruct = 0, TypeInStruct = "ushort")]
            uint sessionId,
            [EventLogMethodParameter(Title = "Session State", OrdinalInStruct = 1, TypeInStruct = "byte")]
            TcpStateEnum sessionState,
            [EventLogMethodParameter(Title = "Timeout Type", OrdinalInStruct = 2, TypeInStruct = "byte")]
            TcpSession.TcpTimeoutType timeoutType)
        {
            if ((debugOptions & LogTimeouts /* To Debugger */) != 0)
            {
                Core.Log("TCP: Ses{0,3} ({1}) Timeout of type '{2}' occurred",
                         sessionId,
                         TcpState.TcpStateNames[(uint)sessionState],
                         TcpSession.TcpTimeoutTypeNames[(uint)timeoutType]);
            }

            if ((ControlFlags & LogTimeouts) != 0)
            {
                TimeoutEntry timeoutEntry =
                    new TimeoutEntry(sessionId, sessionState, timeoutType);

                unsafe
                {
                    return (LogEntry(ControlFlags,
                                     timeoutTypeHandle,
                                     (byte*)&timeoutEntry,
                                     sizeof(TimeoutEntry)) != 0);
                }
            }

            return false;
        }

        //[NoHeapAllocation]
        [EventLogMethod("TcpSessionStateChangeContractCall",
                         HeapAllowed = true,
                         DebugPrint = true,
                         FormatString = "TCP: Ses{0,3} ({1}) Contract EP '{2}' called.")]
        public bool LogSessionStateChangeContractCall(
            [EventLogMethodParameter(Title = "Session", OrdinalInStruct = 0, TypeInStruct = "ushort")]
            uint sessionId,
            [EventLogMethodParameter(Title = "SessionState", OrdinalInStruct = 1, TypeInStruct = "byte")]
            TcpStateEnum sessionState,
            [EventLogMethodParameter(Title = "CallId", OrdinalInStruct = 2, TypeInStruct = "byte")]
            TcpSessionContractEntrypoints contractEntrypoint)
        {
            return this.LogSessionContractCall(sessionId, sessionState,
                                        contractEntrypoint,
                                        LogStateChangeContractCalls);
        }

        //[NoHeapAllocation]
        [EventLogMethod("TcpSessionDataTransferContractCall",
                         HeapAllowed = true,
                         DebugPrint = true,
                         FormatString = "TCP: Ses{0,3} ({1}) Contract EP '{2}' called.")]
        internal bool LogSessionDataTransferContractCall(
            [EventLogMethodParameter(Title = "Session", OrdinalInStruct = 0, TypeInStruct = "ushort")]
            uint sessionId,
            [EventLogMethodParameter(Title = "SessionState", OrdinalInStruct = 1, TypeInStruct = "byte")]
            TcpStateEnum sessionState,
            [EventLogMethodParameter(Title = "CallId", OrdinalInStruct = 2, TypeInStruct = "byte")]
            TcpSessionContractEntrypoints contractEntrypoint)
        {
            return this.LogSessionContractCall(sessionId, sessionState,
                                               contractEntrypoint,
                                               LogDataTransferContractCalls);
        }

        //[NoHeapAllocation]
        [EventLogMethod("TcpSessionQueryContractCall",
                         HeapAllowed = true,
                         DebugPrint = true,
                         FormatString = "TCP: Ses{0,3} ({1}) Contract EP '{2}' called.")]
        internal bool LogSessionQueryContractCall(
            [EventLogMethodParameter(Title = "Session", OrdinalInStruct = 0, TypeInStruct = "ushort")]
            uint sessionId,
            [EventLogMethodParameter(Title = "SessionState", OrdinalInStruct = 1, TypeInStruct = "byte")]
            TcpStateEnum sessionState,
            [EventLogMethodParameter(Title = "CallId", OrdinalInStruct = 2, TypeInStruct = "byte")]
            TcpSessionContractEntrypoints contractEntrypoint)
        {
            return this.LogSessionContractCall(sessionId, sessionState,
                                               contractEntrypoint,
                                               LogQueryContractCalls);
        }

        //[NoHeapAllocation]
        [EventLogMethod("TcpSessionInfoContractCall",
                         HeapAllowed = true,
                         DebugPrint = true,
                         FormatString = "TCP: Ses{0,3} ({1}) Contract EP '{2}' called.")]
        internal bool LogSessionInfoContractCall(
            [EventLogMethodParameter(Title = "Session", OrdinalInStruct = 0, TypeInStruct = "ushort")]
            uint sessionId,
            [EventLogMethodParameter(Title = "SessionState", OrdinalInStruct = 1, TypeInStruct = "byte")]
            TcpStateEnum sessionState,
            [EventLogMethodParameter(Title = "CallId", OrdinalInStruct = 2, TypeInStruct = "byte")]
            TcpSessionContractEntrypoints contractEntrypoint)
        {
            return this.LogSessionContractCall(sessionId, sessionState,
                                               contractEntrypoint,
                                               LogInfoContractCalls);
        }

        //[NoHeapAllocation]
        [EventLogMethod("TcpSessionContractCall",
                         HeapAllowed = true,
                         DebugPrint = true,
                         FormatString = "TCP: Ses{0,3} ({1}) Contract EP '{2}' called.")]
        private bool LogSessionContractCall(
            [EventLogMethodParameter(Title = "Session", OrdinalInStruct = 0, TypeInStruct = "ushort")]
            uint sessionId,
            [EventLogMethodParameter(Title = "SessionState", OrdinalInStruct = 1, TypeInStruct = "byte")]
            TcpStateEnum sessionState,
            [EventLogMethodParameter(Title = "CallName", OrdinalInStruct = 2, TypeInStruct = "byte")]
            TcpSessionContractEntrypoints contractEntrypoint,
            uint flag)
        {
            if ((debugOptions & flag /* To Debugger */) != 0)
            {
                Core.Log("TCP: Ses{0,3} ({1}) Contract EP '{2}' called.",
                         sessionId,
                         TcpState.TcpStateNames[(uint)sessionState],
                         TcpSessionEventsSource.ContractCallNames[(uint)contractEntrypoint]);
            }

            if ((ControlFlags & flag) != 0)
            {
                ContractCallEntry contractCallEntry =
                    new ContractCallEntry(sessionId, sessionState, contractEntrypoint);

                unsafe
                {
                    return (LogEntry(ControlFlags,
                                     contractCallTypeHandle,
                                     (byte*)&contractCallEntry,
                                     sizeof(ContractCallEntry)) != 0);
                }
            }

            return false;
        }

        public override bool Register()
        {
            // Check assumptions for remainder of method.
            if ((base.Register() == false) || (HostController == null))
            {  // BUGBUG AM: base.Register() should check if HostController is null, not all callers
                DebugStub.WriteLine("TcpSessionEventsSource: Improper Registration Environment.");
                return false;
            }

            // TcpSessionStateChange event registration
            if (HostController.RegisterEvent("TcpSessionStateChange",
                                             "TCP: Ses{0,3} ({1}) State Change to {2}.",
                                             ref stateChangeTypeHandle))
            { // BUGBUG AM: Aliases possible with different structs.  Should pass in Struct and Reflect to get name of runtime type, field names, ...
                if ((!HostController.RegisterEventField(stateChangeTypeHandle, "SessionId", 0, DataType.__uint16)) ||
                    (!HostController.RegisterEventField(stateChangeTypeHandle, "FromState", 0, DataType.__uint8)) ||
                    (!HostController.RegisterEventField(stateChangeTypeHandle, "ToState", 0, DataType.__uint8)))
                {
                    stateChangeTypeHandle = 0;
                }
            }

            // TcpSessionReceivedPacket event registration
            if (HostController.RegisterEvent("TcpSessionReceivedPacket",
                                             "TCP: Ses{0,3} ({1}) Packet ({2}) Len{3,4} received",
                                             ref receivedPacketTypeHandle))
            {
                if ((!HostController.RegisterEventField(receivedPacketTypeHandle, "SessionId", 0, DataType.__uint16)) ||
                    (!HostController.RegisterEventField(receivedPacketTypeHandle, "SessionState", 0, DataType.__uint8)) ||
                    (!HostController.RegisterEventField(receivedPacketTypeHandle, "PacketFlags", 0, DataType.__uint8)) ||
                    (!HostController.RegisterEventField(receivedPacketTypeHandle, "PacketLength", 0, DataType.__uint16)))
                {
                    receivedPacketTypeHandle = 0;
                }
            }

            // TcpSessionReceivedPacket event registration
            if (HostController.RegisterEvent("TcpSessionSendingPacket",
                                             "TCP: Ses{0,3} ({1}) Packet ({2}) Len{3,4} being sent",
                                             ref sendingPacketTypeHandle))
            {
                if ((!HostController.RegisterEventField(sendingPacketTypeHandle, "SessionId", 0, DataType.__uint16)) ||
                    (!HostController.RegisterEventField(sendingPacketTypeHandle, "SessionState", 0, DataType.__uint8)) ||
                    (!HostController.RegisterEventField(sendingPacketTypeHandle, "PacketFlags", 0, DataType.__uint8)) ||
                    (!HostController.RegisterEventField(sendingPacketTypeHandle, "PacketLength", 0, DataType.__uint16)))
                {
                    sendingPacketTypeHandle = 0;
                }
            }

            // TcpSessionTimeout event registration
            if (HostController.RegisterEvent("TcpSessionTimeout",
                                             "TCP: Ses{0,3} ({1}) Timeout of type '{2}' occurred",
                                             ref timeoutTypeHandle))
            {
                if ((!HostController.RegisterEventField(timeoutTypeHandle, "SessionId", 0, DataType.__uint16)) ||
                    (!HostController.RegisterEventField(timeoutTypeHandle, "SessionState", 0, DataType.__uint8)) ||
                    (!HostController.RegisterEventField(timeoutTypeHandle, "TimeoutType", 0, DataType.__uint8)))
                {
                    timeoutTypeHandle = 0;
                }
            }

            // TcpSessionContractCall event registration
            if (HostController.RegisterEvent("TcpSessionContractCall",
                                             "TCP: Ses{0,3} ({1}) Contract EP '{2}' called.",
                                             ref contractCallTypeHandle))
            {
                if ((!HostController.RegisterEventField(contractCallTypeHandle, "SessionId", 0, DataType.__uint16)) ||
                    (!HostController.RegisterEventField(contractCallTypeHandle, "SessionState", 0, DataType.__uint8)) ||
                    (!HostController.RegisterEventField(contractCallTypeHandle, "ContractCall", 0, DataType.__uint8)))
                {
                    contractCallTypeHandle = 0;
                }
            }

            // Make sure all handles were either there before or were created here.
            if ((stateChangeTypeHandle == 0) || (contractCallTypeHandle == 0) ||
                (sendingPacketTypeHandle == 0) || (sendingPacketTypeHandle == 0))
            {
                // Construct an error message
                StringBuilder errorString = new StringBuilder();
                String conjunction = "TcpSessionEventsSource: Registration Failed for ";

                // State Change
                if (stateChangeTypeHandle == 0)
                {
                    errorString.Append(conjunction);
                    errorString.Append("StateChangeEventType");
                    conjunction = ", ";
                }

                // Received Packet
                if (receivedPacketTypeHandle == 0)
                {
                    errorString.Append(conjunction);
                    errorString.Append("ReceivedPacketEventType");
                    conjunction = ", ";
                }

                // Sending Packet
                if (sendingPacketTypeHandle == 0)
                {
                    errorString.Append(conjunction);
                    errorString.Append("SendingPacketEventType");
                    conjunction = ", ";
                }

                // Timeout
                if (timeoutTypeHandle == 0)
                {
                    errorString.Append(conjunction);
                    errorString.Append("TimeoutEventType");
                    conjunction = ", ";
                }

                // Contract Call
                if (contractCallTypeHandle == 0)
                {
                    errorString.Append(conjunction);
                    errorString.Append("ContractCallEventType");
                    conjunction = ", ";
                }

                // Complete the error message and write it to the debugger.
                errorString.Append(".");
                errorString.Append(Environment.NewLine);
                DebugStub.Write(errorString.ToString());

                // Report the failure.
                return false;
            }

            // If this is reached then everything worked so report success.
            return true;
        }

        [Pure]
        [Inline]
        private static string FlagsToText(uint flags)
        {
            string[] loBits = new string[] {
                "....", "F...", ".S..", "FS..",
                "..R.", "F.R.", ".SR.", "FSR.",
                "...P", "F..P", ".S.P", "FS.P",
                "..RP", "F.RP", ".SRP", "FSRP",
            };
            string[] hiBits = new string[] {
                "....", "A...", ".I..", "AI..",
                "..E.", "A.E.", ".IE.", "AIE.",
                "...C", "A..C", ".I.C", "AI.C",
                "..EC", "A.EC", ".IEC", "AIEC",
            };

            return loBits[(flags >> 0) & 0x0F] + hiBits[(flags >> 4) & 0x0F];
        }
    }
}

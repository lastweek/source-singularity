///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DhcpOptions.cs
//
//  Note: Partial RFC1533 implementation.
//

using NetStack.Common;
using System;
using System.Collections;

using System.Net.IP;
using Drivers.Net;

namespace NetStack.Protocols
{
    public interface IDhcpOption
    {
        byte OptionCode { get; }
        int  PayloadLength { get; }
        int  Pack(byte[]! dstBuffer, ref int offset);
    }

    public class InvalidDhcpOptionLength : SystemException
    {
        public InvalidDhcpOptionLength()
            : base()
        {
        }

        public InvalidDhcpOptionLength(String message)
            : base(message)
        {
        }

        public InvalidDhcpOptionLength(String message,
                                       Exception innerException)
            : base(message, innerException)
        {
        }

        public InvalidDhcpOptionLength(String format, params object [] args)
            : base (String.Format(format, args))
        {
        }
    }

    public class DhcpIPv4Option : IDhcpOption
    {
        private byte option;
        private IPv4 address;

        private const int payloadLength = 4;

        public DhcpIPv4Option(byte option, IPv4 address)
        {
            this.option  = option;
            this.address = address;
        }

        public byte OptionCode
        {
            get { return option; }
        }

        public int PayloadLength
        {
            get { return payloadLength; }
        }

        public IPv4 Value
        {
            get { return address; }
        }

        public int Pack(byte[]! dstBuffer, ref int offset)
        {
            dstBuffer[offset++] = option;
            dstBuffer[offset++] = (byte)payloadLength;
            byte[] b = address.GetAddressBytes();
            dstBuffer[offset++] = b[0];
            dstBuffer[offset++] = b[1];
            dstBuffer[offset++] = b[2];
            dstBuffer[offset++] = b[3];
            return payloadLength + 2;
        }

        public static IDhcpOption! Parse(byte option,
                                         byte length,
                                         byte[]! srcBuffer,
                                         int  offset)
        {
            if (length != payloadLength) {
                throw new InvalidDhcpOptionLength();
            }
            return new DhcpIPv4Option(option,
                                      IPv4.ParseBytes(srcBuffer, offset));
        }
    }

    public class DhcpMultiIPv4Option : IDhcpOption
    {
        private byte option;
        private IPv4 []! addresses;

        public DhcpMultiIPv4Option(byte option, IPv4 []! addresses)
        {
            this.option    = option;
            this.addresses = addresses;
            base();
        }

        public byte OptionCode
        {
            get { return option; }
        }

        public int PayloadLength
        {
            get { return addresses.Length * 4; }
        }

        public IPv4[]! Values
        {
            get { return addresses; }
        }

        public int Pack(byte[]! dstBuffer, ref int offset)
        {
            dstBuffer[offset++] = option;
            dstBuffer[offset++] = (byte)(addresses.Length * 4);
            foreach (IPv4 address in addresses) {
                address.CopyOut(dstBuffer, offset);
                offset += IPv4.Length;
            }
            return addresses.Length * 4 + 2;
        }

        public static IDhcpOption! Parse(byte option, byte length,
                                         byte[]! srcBuffer, int offset)
        {
            if ((length & 3) != 0) {
                throw new InvalidDhcpOptionLength();
            }
            IPv4 [] addresses = new IPv4 [length / 4];
            for (int i = 0; i < addresses.Length; i++) {
                addresses[i]  = IPv4.ParseBytes(srcBuffer, offset);
                offset       += IPv4.Length;
            }
            return new DhcpMultiIPv4Option(option, addresses);
        }
    }

    public class DhcpByteOption : IDhcpOption
    {
        private byte value;
        private byte option;

        private const int payloadLength = 1;

        public DhcpByteOption(byte option, byte value)
        {
            this.option = option;
            this.value  = value;
        }

        public byte OptionCode
        {
            get { return option; }
        }

        public int PayloadLength
        {
            get { return payloadLength; }
        }

        public byte Value
        {
            get { return value; }
        }

        public int Pack(byte[]! dstBuffer, ref int offset)
        {
            dstBuffer[offset++] = option;
            dstBuffer[offset++] = (byte)payloadLength;
            dstBuffer[offset++] = value;
            return payloadLength + 2;
        }

        public static IDhcpOption! Parse(byte option, byte length,
                                         byte[]! srcBuffer, int offset)
        {
            byte value  = srcBuffer[offset];
            return new DhcpByteOption(option, value);
        }
    }

    public class DhcpMultiByteOption : IDhcpOption
    {
        private byte option;
        private byte [] values;

        public DhcpMultiByteOption(byte option, byte [] values)
        {
            this.option = option;
            this.values = values;
        }

        public byte OptionCode
        {
            get { return option; }
        }

        public int PayloadLength
        {
            get { return values.Length; }
        }

        public byte[] Values
        {
            get { return values; }
        }

        public int Pack(byte[]! dstBuffer, ref int offset)
        {
            dstBuffer[offset++] = option;
            dstBuffer[offset++] = (byte)values.Length;
            foreach (byte value in this.values) {
                dstBuffer[offset++] = value;
            }
            return values.Length + 2;
        }

        public static IDhcpOption! Parse(byte option, byte length,
                                         byte[]! srcBuffer, int offset)
        {
            byte [] values = new byte [length];
            for (int i = 0; i < values.Length; i++) {
                values[i] = srcBuffer[offset++];
            }
            return new DhcpMultiByteOption(option, values);
        }
    }

    public class DhcpStringOption : IDhcpOption
    {
        private byte option;
        private char [] chars;

        public DhcpStringOption(byte option, char [] chars)
        {
            this.option = option;
            this.chars = chars;
        }

        public byte OptionCode
        {
            get { return option; }
        }

        public int PayloadLength
        {
            get { return chars.Length; }
        }

        public string! Value
        {
            get { return new string(chars); }
        }

        public int Pack(byte[]! dstBuffer, ref int offset)
        {
            dstBuffer[offset++] = option;
            dstBuffer[offset++] = (byte)chars.Length;
            foreach (char c in this.chars) {
                dstBuffer[offset++] = (byte)c;
            }
            // NB We do not zero-terminate string as options
            // have a length field.  However, see some
            // zero-terminated strings in the wild (???)
            return chars.Length + 2;
        }

        public static IDhcpOption! Parse(byte option, byte length,
                                         byte[]! srcBuffer, int offset)
        {
            int end;

            for (end = offset; end < offset + length; end++)
                if (srcBuffer[end] < 32)
                    break;

            char [] chars = new char [end - offset];
            for (int i = 0; i < chars.Length; i++) {
                chars[i] = (char)srcBuffer[offset + i];
            }
            return new DhcpStringOption(option, chars);
        }
    }

    public class DhcpWordOption : IDhcpOption
    {
        private byte option;
        private ushort value;

        private const int payloadLength = 2;

        public DhcpWordOption(byte option, ushort value)
        {
            this.option = option;
            this.value  = value;
        }

        public byte OptionCode
        {
            get { return option; }
        }

        public int PayloadLength
        {
            get { return payloadLength; }
        }

        public ushort Value
        {
            get { return value; }
        }

        public int Pack(byte[]! dstBuffer, ref int offset)
        {
            dstBuffer[offset++] = option;
            dstBuffer[offset++] = (byte)payloadLength;
            dstBuffer[offset++] = (byte)(value >> 8);
            dstBuffer[offset++] = (byte)value;
            return payloadLength + 2;
        }

        public static IDhcpOption! Parse(byte option, byte length,
                                         byte[]! srcBuffer, int offset)
        {
            if (length != payloadLength) {
                throw new InvalidDhcpOptionLength();
            }
            int value = ((int)srcBuffer[offset++]) << 8;
            value    |= (int)srcBuffer[offset];
            return new DhcpWordOption(option, (ushort)value);
        }
    }

    public class DhcpMultiWordOption : IDhcpOption
    {
        private ushort[] values;
        private byte option;

        public DhcpMultiWordOption(byte option, ushort[] values)
        {
            this.option = option;
            this.values = values;
        }

        public byte OptionCode
        {
            get { return option; }
        }

        public int PayloadLength
        {
            get { return 2 * values.Length; }
        }

        public ushort[] Values
        {
            get { return values; }
        }

        public int Pack(byte[]! dstBuffer, ref int offset)
        {
            dstBuffer[offset++] = option;
            dstBuffer[offset++] = (byte)(2 * values.Length);

            foreach (ushort value in values) {
                dstBuffer[offset++] = (byte)(value >> 8);
                dstBuffer[offset++] = (byte)value;
            }
            return 2 * values.Length + 2;
        }

        public static IDhcpOption! Parse(byte option, byte length,
                                         byte[]! srcBuffer, int offset)
        {
            if ((length & 1) != 0) {
                throw new InvalidDhcpOptionLength();
            }

            ushort [] values = new ushort [length / 2];
            for (int i = 0; i < values.Length; i++) {
                int tmp = ((int)srcBuffer[offset++]) << 8;
                tmp    += (int)srcBuffer[offset++];
                values[i] = (ushort)tmp;
            }
            return new DhcpMultiWordOption(option, values);
        }
    }

    public class DhcpDWordOption : IDhcpOption
    {
        private byte option;
        private uint value;

        private const int payloadLength = 4;

        public DhcpDWordOption(byte option, uint value)
        {
            this.option = option;
            this.value  = value;
        }

        public byte OptionCode
        {
            get { return option; }
        }

        public int PayloadLength
        {
            get { return payloadLength; }
        }

        public uint Value
        {
            get { return value; }
        }

        public int Pack(byte[]! dstBuffer, ref int offset)
        {
            dstBuffer[offset++] = option;
            dstBuffer[offset++] = (byte)payloadLength;
            dstBuffer[offset++] = (byte)(value >> 24);
            dstBuffer[offset++] = (byte)(value >> 16);
            dstBuffer[offset++] = (byte)(value >> 8);
            dstBuffer[offset++] = (byte)value;
            return payloadLength + 2;
        }

        public static IDhcpOption! Parse(byte option, byte length,
                                         byte[]! srcBuffer, int offset)
        {
            if (length != 4) {
                throw new InvalidDhcpOptionLength();
            }
            int value = ((int)srcBuffer[offset++]) << 24;
            value    |= ((int)srcBuffer[offset++]) << 16;
            value    |= ((int)srcBuffer[offset++]) << 8;
            value    |= ((int)srcBuffer[offset]);
            return new DhcpDWordOption(option, (uint)value);
        }
    }

    public class DhcpMultiDWordOption : IDhcpOption
    {
        private uint[] values;
        private byte option;

        public DhcpMultiDWordOption(byte option, uint[] values)
        {
            this.option = option;
            this.values = values;
        }

        public byte OptionCode
        {
            get { return option; }
        }

        public int PayloadLength
        {
            get { return 4 * values.Length; }
        }

        public uint[] Values
        {
            get { return values; }
        }

        public int Pack(byte[]! dstBuffer, ref int offset)
        {
            dstBuffer[offset++] = option;
            dstBuffer[offset++] = (byte)(4 * values.Length);

            foreach (uint value in values) {
                dstBuffer[offset++] = (byte)(value >> 24);
                dstBuffer[offset++] = (byte)(value >> 16);
                dstBuffer[offset++] = (byte)(value >> 8);
                dstBuffer[offset++] = (byte)value;
            }
            return 4 * values.Length + 2;
        }

        public static IDhcpOption! Parse(byte option, byte length,
                                         byte[]! srcBuffer, int offset)
        {
            if ((length & 3) != 0) {
                throw new InvalidDhcpOptionLength();
            }

            uint [] values = new uint [length / 4];
            for (int i = 0; i < values.Length; i++) {
                values[i]  = ((uint)srcBuffer[offset++]) << 24;
                values[i] |= ((uint)srcBuffer[offset++]) << 16;
                values[i] |= ((uint)srcBuffer[offset++]) << 8;
                values[i] |= ((uint)srcBuffer[offset++]);
            }
            return new DhcpMultiDWordOption(option, values);
        }
    }

    public delegate IDhcpOption! ParseDhcpOption(byte type,
                                                 byte length,
                                                 byte[]! srcBuffer,
                                                 int offset);

    public class DhcpOptionParser
    {
        static SortedList parsers;

        internal class Parser
        {
            public string OptionName;
            public ParseDhcpOption Parse;

            public Parser(string optionName, ParseDhcpOption parseMethod)
            {
                this.OptionName = optionName;
                this.Parse = parseMethod;
            }
        };

        public static string GetOptionName(byte optionCode)
        {
            Parser parser = (Parser) parsers[optionCode];
            if (parser != null) {
                return parser.OptionName;
            }
            return "Unknown";
        }

        public static SortedList! Parse(byte[]! data, int offset, int length)
        {
            const byte PadByte = 0;
            const byte EndByte = 255;
            SortedList dhcpOptions = new SortedList();

            while (offset != length) {
                // skip padding
                while (data[offset] == PadByte) {
                    offset++;
                    if (offset == length) {
                        goto finished_options;
                    }
                }

                if (data[offset] == EndByte) {
                    break;
                }

                byte @opt   = data[offset++];
                byte optlen = data[offset++];

                if (optlen == 0) {
                    // Unknown, ignore
                    continue;
                }

                if (optlen + offset > length) {
                    break;
                }

                // Remove any outstanding option with the same option number
                // before adding option to list of those already parsed to
                // prevent SortedList::Add from throwing ArgumentException
                dhcpOptions.Remove(opt);
                try {
                    Parser parser = (Parser) parsers[@opt];
                    if (parser != null) {
                        dhcpOptions.Add(
                            opt, parser.Parse(@opt, optlen, data, offset)
                            );
                    }
                    else {
                        // For unknowns fall back to multi-byte parser
                        dhcpOptions.Add(
                            @opt, DhcpMultiByteOption.Parse(@opt, optlen,
                                                            data, offset)
                            );
                    }
                }
                catch (InvalidDhcpOptionLength) {
                }
                offset += optlen;
            }
          finished_options:
            return dhcpOptions;
        }

        public static SortedList! Parse(IBuffer! buffer)
        {
            // This is an unnecessary copy
            byte [] data = new byte [buffer.Available];
            buffer.ReadBytes(data, 0, data.Length);
            return Parse(data, 0, data.Length);
        }

        static DhcpOptionParser()
        {
            parsers     = new SortedList();
#region GeneratedTable
            parsers.Add(DhcpSubnetMask.OptionCode,
                        new Parser("SubnetMask",
                                   new ParseDhcpOption(DhcpIPv4Option.Parse)));
            parsers.Add(DhcpTimeOffset.OptionCode,
                        new Parser("TimeOffset",
                                   new ParseDhcpOption(DhcpDWordOption.Parse)));
            parsers.Add(DhcpRouter.OptionCode,
                        new Parser("Router",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpTimeServer.OptionCode,
                        new Parser("TimeServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpNameServer.OptionCode,
                        new Parser("NameServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpDomainNameServer.OptionCode,
                        new Parser("DomainNameServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpLogServer.OptionCode,
                        new Parser("LogServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpCookieServer.OptionCode,
                        new Parser("CookieServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpLprServer.OptionCode,
                        new Parser("LprServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpImpressServer.OptionCode,
                        new Parser("ImpressServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpResourceLocationServer.OptionCode,
                        new Parser("ResourceLocationServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpHostName.OptionCode,
                        new Parser("HostName",
                                   new ParseDhcpOption(DhcpStringOption.Parse)));
            parsers.Add(DhcpBootFileSize.OptionCode,
                        new Parser("BootFileSize",
                                   new ParseDhcpOption(DhcpWordOption.Parse)));
            parsers.Add(DhcpMeritDumpFile.OptionCode,
                        new Parser("MeritDumpFile",
                                   new ParseDhcpOption(DhcpStringOption.Parse)));
            parsers.Add(DhcpDomainName.OptionCode,
                        new Parser("DomainName",
                                   new ParseDhcpOption(DhcpStringOption.Parse)));
            parsers.Add(DhcpSwapServer.OptionCode,
                        new Parser("SwapServer",
                                   new ParseDhcpOption(DhcpIPv4Option.Parse)));
            parsers.Add(DhcpRootPath.OptionCode,
                        new Parser("RootPath",
                                   new ParseDhcpOption(DhcpStringOption.Parse)));
            parsers.Add(DhcpExtensionsPath.OptionCode,
                        new Parser("ExtensionsPath",
                                   new ParseDhcpOption(DhcpStringOption.Parse)));
            parsers.Add(DhcpIPForwarding.OptionCode,
                        new Parser("IPForwarding",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpForwardRemoteSourceRoute.OptionCode,
                        new Parser("ForwardRemoteSourceRoute",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpPolicyFilter.OptionCode,
                        new Parser("PolicyFilter",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpMaximumDatagramReassembly.OptionCode,
                        new Parser("MaximumDatagramReassembly",
                                   new ParseDhcpOption(DhcpWordOption.Parse)));
            parsers.Add(DhcpDefaultTtl.OptionCode,
                        new Parser("DefaultTtl",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpPathMtuAgingTimeout.OptionCode,
                        new Parser("PathMtuAgingTimeout",
                                   new ParseDhcpOption(DhcpDWordOption.Parse)));
            parsers.Add(DhcpPathMtuPlateauTable.OptionCode,
                        new Parser("PathMtuPlateauTable",
                                   new ParseDhcpOption(DhcpMultiWordOption.Parse)));
            parsers.Add(DhcpInterfaceMtu.OptionCode,
                        new Parser("InterfaceMtu",
                                   new ParseDhcpOption(DhcpWordOption.Parse)));
            parsers.Add(DhcpAllSubnetsLocal.OptionCode,
                        new Parser("AllSubnetsLocal",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpBroadcastAddress.OptionCode,
                        new Parser("BroadcastAddress",
                                   new ParseDhcpOption(DhcpIPv4Option.Parse)));
            parsers.Add(DhcpMaskDiscovery.OptionCode,
                        new Parser("MaskDiscovery",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpMaskSupplier.OptionCode,
                        new Parser("MaskSupplier",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpRouterDiscovery.OptionCode,
                        new Parser("RouterDiscovery",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpRouterSolicitationAddress.OptionCode,
                        new Parser("RouterSolicitationAddress",
                                   new ParseDhcpOption(DhcpIPv4Option.Parse)));
            parsers.Add(DhcpStaticRoutes.OptionCode,
                        new Parser("StaticRoutes",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpTrailerEncapsulate.OptionCode,
                        new Parser("TrailerEncapsulate",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpArpCacheTimeout.OptionCode,
                        new Parser("ArpCacheTimeout",
                                   new ParseDhcpOption(DhcpDWordOption.Parse)));
            parsers.Add(DhcpEthernetEncapsulation.OptionCode,
                        new Parser("EthernetEncapsulation",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpTcpDefaultTtl.OptionCode,
                        new Parser("TcpDefaultTtl",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpTcpKeepalive.OptionCode,
                        new Parser("TcpKeepalive",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpTcpKeepaliveGarbage.OptionCode,
                        new Parser("TcpKeepaliveGarbage",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpNisDomain.OptionCode,
                        new Parser("NisDomain",
                                   new ParseDhcpOption(DhcpStringOption.Parse)));
            parsers.Add(DhcpNisServers.OptionCode,
                        new Parser("NisServers",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpNtpServers.OptionCode,
                        new Parser("NtpServers",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpVendorSpecific.OptionCode,
                        new Parser("VendorSpecific",
                                   new ParseDhcpOption(DhcpMultiByteOption.Parse)));
            parsers.Add(DhcpNetBiosNameServer.OptionCode,
                        new Parser("NetBiosNameServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpNetBiosDistributionServer.OptionCode,
                        new Parser("NetBiosDistributionServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpNetBiosType.OptionCode,
                        new Parser("NetBiosType",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpNetBiosScope.OptionCode,
                        new Parser("NetBiosScope",
                                   new ParseDhcpOption(DhcpMultiDWordOption.Parse)));
            parsers.Add(DhcpXWindowsFontServer.OptionCode,
                        new Parser("XWindowsFontServer",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpXWindowsDisplayManager.OptionCode,
                        new Parser("XWindowsDisplayManager",
                                   new ParseDhcpOption(DhcpMultiIPv4Option.Parse)));
            parsers.Add(DhcpRequestedIPAddress.OptionCode,
                        new Parser("RequestedIPAddress",
                                   new ParseDhcpOption(DhcpIPv4Option.Parse)));
            parsers.Add(DhcpIPAddressLeaseTime.OptionCode,
                        new Parser("IPAddressLeaseTime",
                                   new ParseDhcpOption(DhcpDWordOption.Parse)));
            parsers.Add(DhcpOverloadIndicator.OptionCode,
                        new Parser("OverloadIndicator",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpMessageType.OptionCode,
                        new Parser("MessageType",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
            parsers.Add(DhcpServerID.OptionCode,
                        new Parser("ServerID",
                                   new ParseDhcpOption(DhcpIPv4Option.Parse)));
            parsers.Add(DhcpParameterRequest.OptionCode,
                        new Parser("ParameterRequest",
                                   new ParseDhcpOption(DhcpMultiByteOption.Parse)));
            parsers.Add(DhcpMessage.OptionCode,
                        new Parser("Message",
                                   new ParseDhcpOption(DhcpStringOption.Parse)));
            parsers.Add(DhcpMaximumMessageSize.OptionCode,
                        new Parser("MaximumMessageSize",
                                   new ParseDhcpOption(DhcpWordOption.Parse)));
            parsers.Add(DhcpRenewalTime.OptionCode,
                        new Parser("RenewalTime",
                                   new ParseDhcpOption(DhcpDWordOption.Parse)));
            parsers.Add(DhcpRebindingTime.OptionCode,
                        new Parser("RebindingTime",
                                   new ParseDhcpOption(DhcpDWordOption.Parse)));
            parsers.Add(DhcpClassID.OptionCode,
                        new Parser("ClassID",
                                   new ParseDhcpOption(DhcpStringOption.Parse)));
            parsers.Add(DhcpClientID.OptionCode,
                        new Parser("ClientID",
                                   new ParseDhcpOption(DhcpMultiByteOption.Parse)));
            parsers.Add(DhcpAutoConfigure.OptionCode,
                        new Parser("AutoConfigure",
                                   new ParseDhcpOption(DhcpByteOption.Parse)));
#endregion // GeneratedTable
        }

        private DhcpOptionParser()
        {
        }
    }

    //
    // FOR THE FOLLOWING REGION EDIT THE CODE GENERATOR
    // NOT THE GENERATED CODE...
    //
#region GeneratedClasses

    public class DhcpSubnetMask
    {
        public const byte OptionCode = 1;

        public static IDhcpOption! Create(IPv4 address)
        {
            return new DhcpIPv4Option(OptionCode, address);
        }
     }

    public class DhcpTimeOffset
    {
        public const byte OptionCode = 2;

        public static IDhcpOption! Create(uint value)
        {
            return new DhcpDWordOption(OptionCode, value);
        }
     }

    public class DhcpRouter
    {
        public const byte OptionCode = 3;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpTimeServer
    {
        public const byte OptionCode = 4;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpNameServer
    {
        public const byte OptionCode = 5;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpDomainNameServer
    {
        public const byte OptionCode = 6;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpLogServer
    {
        public const byte OptionCode = 7;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpCookieServer
    {
        public const byte OptionCode = 8;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpLprServer
    {
        public const byte OptionCode = 9;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpImpressServer
    {
        public const byte OptionCode = 10;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpResourceLocationServer
    {
        public const byte OptionCode = 11;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpHostName
    {
        public const byte OptionCode = 12;

        public static IDhcpOption! Create(char [] chars)
        {
            return new DhcpStringOption(OptionCode, chars);
        }
     }

    public class DhcpBootFileSize
    {
        public const byte OptionCode = 13;

        public static IDhcpOption! Create(ushort value)
        {
            return new DhcpWordOption(OptionCode, value);
        }
     }

    public class DhcpMeritDumpFile
    {
        public const byte OptionCode = 14;

        public static IDhcpOption! Create(char [] chars)
        {
            return new DhcpStringOption(OptionCode, chars);
        }
     }

    public class DhcpDomainName
    {
        public const byte OptionCode = 15;

        public static IDhcpOption! Create(char [] chars)
        {
            return new DhcpStringOption(OptionCode, chars);
        }
     }

    public class DhcpSwapServer
    {
        public const byte OptionCode = 16;

        public static IDhcpOption! Create(IPv4 address)
        {
            return new DhcpIPv4Option(OptionCode, address);
        }
     }

    public class DhcpRootPath
    {
        public const byte OptionCode = 17;

        public static IDhcpOption! Create(char [] chars)
        {
            return new DhcpStringOption(OptionCode, chars);
        }
     }

    public class DhcpExtensionsPath
    {
        public const byte OptionCode = 18;

        public static IDhcpOption! Create(char [] chars)
        {
            return new DhcpStringOption(OptionCode, chars);
        }
     }

    public class DhcpIPForwarding
    {
        public const byte OptionCode = 19;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpForwardRemoteSourceRoute
    {
        public const byte OptionCode = 20;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpPolicyFilter
    {
        public const byte OptionCode = 21;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpMaximumDatagramReassembly
    {
        public const byte OptionCode = 22;

        public static IDhcpOption! Create(ushort value)
        {
            return new DhcpWordOption(OptionCode, value);
        }
     }

    public class DhcpDefaultTtl
    {
        public const byte OptionCode = 23;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpPathMtuAgingTimeout
    {
        public const byte OptionCode = 24;

        public static IDhcpOption! Create(uint value)
        {
            return new DhcpDWordOption(OptionCode, value);
        }
     }

    public class DhcpPathMtuPlateauTable
    {
        public const byte OptionCode = 25;

        public static IDhcpOption! Create(ushort [] values)
        {
            return new DhcpMultiWordOption(OptionCode, values);
        }
     }

    public class DhcpInterfaceMtu
    {
        public const byte OptionCode = 26;

        public static IDhcpOption! Create(ushort value)
        {
            return new DhcpWordOption(OptionCode, value);
        }
     }

    public class DhcpAllSubnetsLocal
    {
        public const byte OptionCode = 27;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpBroadcastAddress
    {
        public const byte OptionCode = 28;

        public static IDhcpOption! Create(IPv4 address)
        {
            return new DhcpIPv4Option(OptionCode, address);
        }
     }

    public class DhcpMaskDiscovery
    {
        public const byte OptionCode = 29;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpMaskSupplier
    {
        public const byte OptionCode = 30;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpRouterDiscovery
    {
        public const byte OptionCode = 31;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpRouterSolicitationAddress
    {
        public const byte OptionCode = 32;

        public static IDhcpOption! Create(IPv4 address)
        {
            return new DhcpIPv4Option(OptionCode, address);
        }
     }

    public class DhcpStaticRoutes
    {
        public const byte OptionCode = 33;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpTrailerEncapsulate
    {
        public const byte OptionCode = 34;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpArpCacheTimeout
    {
        public const byte OptionCode = 35;

        public static IDhcpOption! Create(uint value)
        {
            return new DhcpDWordOption(OptionCode, value);
        }
     }

    public class DhcpEthernetEncapsulation
    {
        public const byte OptionCode = 36;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpTcpDefaultTtl
    {
        public const byte OptionCode = 37;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpTcpKeepalive
    {
        public const byte OptionCode = 38;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpTcpKeepaliveGarbage
    {
        public const byte OptionCode = 39;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpNisDomain
    {
        public const byte OptionCode = 40;

        public static IDhcpOption! Create(char [] chars)
        {
            return new DhcpStringOption(OptionCode, chars);
        }
     }

    public class DhcpNisServers
    {
        public const byte OptionCode = 41;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpNtpServers
    {
        public const byte OptionCode = 42;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpVendorSpecific
    {
        public const byte OptionCode = 43;

        public static IDhcpOption! Create(byte [] values)
        {
            return new DhcpMultiByteOption(OptionCode, values);
        }
     }

    public class DhcpNetBiosNameServer
    {
        public const byte OptionCode = 44;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpNetBiosDistributionServer
    {
        public const byte OptionCode = 45;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpNetBiosType
    {
        public const byte OptionCode = 46;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpNetBiosScope
    {
        public const byte OptionCode = 47;

        public static IDhcpOption! Create(uint [] values)
        {
            return new DhcpMultiDWordOption(OptionCode, values);
        }
     }

    public class DhcpXWindowsFontServer
    {
        public const byte OptionCode = 48;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpXWindowsDisplayManager
    {
        public const byte OptionCode = 49;

        public static IDhcpOption! Create(IPv4[]! addresses)
        {
            return new DhcpMultiIPv4Option(OptionCode, addresses);
        }
     }

    public class DhcpRequestedIPAddress
    {
        public const byte OptionCode = 50;

        public static IDhcpOption! Create(IPv4 address)
        {
            return new DhcpIPv4Option(OptionCode, address);
        }
     }

    public class DhcpIPAddressLeaseTime
    {
        public const byte OptionCode = 51;

        public static IDhcpOption! Create(uint value)
        {
            return new DhcpDWordOption(OptionCode, value);
        }
     }

    public class DhcpOverloadIndicator
    {
        public const byte OptionCode = 52;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpMessageType
    {
        public const byte OptionCode = 53;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }

    public class DhcpServerID
    {
        public const byte OptionCode = 54;

        public static IDhcpOption! Create(IPv4 address)
        {
            return new DhcpIPv4Option(OptionCode, address);
        }
     }

    public class DhcpParameterRequest
    {
        public const byte OptionCode = 55;

        public static IDhcpOption! Create(byte [] values)
        {
            return new DhcpMultiByteOption(OptionCode, values);
        }
     }

    public class DhcpMessage
    {
        public const byte OptionCode = 56;

        public static IDhcpOption! Create(char [] chars)
        {
            return new DhcpStringOption(OptionCode, chars);
        }
     }

    public class DhcpMaximumMessageSize
    {
        public const byte OptionCode = 57;

        public static IDhcpOption! Create(ushort value)
        {
            return new DhcpWordOption(OptionCode, value);
        }
     }

    public class DhcpRenewalTime
    {
        public const byte OptionCode = 58;

        public static IDhcpOption! Create(uint value)
        {
            return new DhcpDWordOption(OptionCode, value);
        }
     }

    public class DhcpRebindingTime
    {
        public const byte OptionCode = 59;

        public static IDhcpOption! Create(uint value)
        {
            return new DhcpDWordOption(OptionCode, value);
        }
     }

    public class DhcpClassID
    {
        public const byte OptionCode = 60;

        public static IDhcpOption! Create(char [] chars)
        {
            return new DhcpStringOption(OptionCode, chars);
        }
     }

    public class DhcpClientID
    {
        public const byte OptionCode = 61;

        public static IDhcpOption! Create(byte [] values)
        {
            return new DhcpMultiByteOption(OptionCode, values);
        }
     }

    public class DhcpAutoConfigure
    {
        public const byte OptionCode = 116;

        public static IDhcpOption! Create(byte value)
        {
            return new DhcpByteOption(OptionCode, value);
        }
     }
#endregion // GeneratedClasses
}

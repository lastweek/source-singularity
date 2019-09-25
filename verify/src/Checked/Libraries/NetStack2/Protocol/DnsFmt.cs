///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DnsFmt.cs
//
//  Note:
//
//      Constants taken from http://www.iana.org/assignments/dns-parameters
//
//  Caveat Emptor:
//
//      This implementation only supports message compression for messages
//      received and not for outbound messages. (RFC1035 section 4.1.4)
//

using System;
using System.Collections;
using System.Text;
using System.Diagnostics;

using System.Net.IP;
using Drivers.Net;

using Microsoft.Contracts;

namespace Microsoft.Singularity.NetStack2.Protocols.Dns
{
    public enum Class : ushort
    {
        // 0 Reserved             // [IANA]
        Internet = 1,             // [RFC1035]
        // 2 Unassigned           // [IANA]
        Chaos    = 3,             // [RFC1035]
        Hesiod   = 4,             // [RFC1035]
        // 5-253 Unassigned       // [IANA]
        None     = 254,           // [RFC2136]
        Any      = 255            // [RFC1035]
        // 256-65534 Unassigned   // [IANA]
        // 65535 Reserved         // [IANA]
    }

    public enum Type : ushort
    {
        A       = 1,    // a host address                          [RFC1035]
        NS      = 2,    // an authoritative name server            [RFC1035]
        MD      = 3,    // a mail destination (Obsolete - use MX)  [RFC1035]
        MF      = 4,    // a mail forwarder (Obsolete - use MX)    [RFC1035]
        CNAME   = 5,    // the canonical name for an alias         [RFC1035]
        SOA     = 6,    // marks the start of a zone of authority  [RFC1035]
        MB      = 7,    // a mailbox domain name (EXPERIMENTAL)    [RFC1035]
        MG      = 8,    // a mail group member (EXPERIMENTAL)      [RFC1035]
        MR      = 9,    // a mail rename domain name (EXPERIMENTAL)[RFC1035]
        NULL    = 10,    // a null RR (EXPERIMENTAL)               [RFC1035]
        WKS     = 11,    // a well known service description       [RFC1035]
        PTR     = 12,    // a domain name pointer                  [RFC1035]
        HINFO   = 13,    // host information                       [RFC1035]
        MINFO   = 14,    // mailbox or mail list information       [RFC1035]
        MX      = 15,    // mail exchange                          [RFC1035]
        TXT     = 16,    // text strings                           [RFC1035]
        RP      = 17,    // for Responsible Person                 [RFC1183]
        AFSDB   = 18,    // for AFS Data Base location             [RFC1183]
        X25     = 19,    // for X.25 PSDN address                  [RFC1183]
        ISDN    = 20,    // for ISDN address                       [RFC1183]
        RT      = 21,    // for Route Through                      [RFC1183]
        NSAP    = 22,    // for NSAP address, NSAP style A record  [RFC1706]
        NSAPPTR = 23,
        SIG     = 24,    // for security signature                 [RFC2931]
        KEY     = 25,    // for security key                       [RFC2535]
        PX      = 26,    // X.400 mail mapping information         [RFC2163]
        GPOS    = 27,    // Geographical Position                  [RFC1712]
        AAAA    = 28,    // IP6 Address                            [Thomson]
        LOC     = 29,    // Location Information                   [Vixie]
        NXT     = 30,    // Next Domain - OBSOLETE        [RFC2535, RFC3755]
        EID     = 31,    // Endpoint Identifier                    [Patton]
        NIMLOC  = 32,    // Nimrod Locator                         [Patton]
        SRV     = 33,    // Server Selection                       [RFC2782]
        ATMA    = 34,    // ATM Address                            [Dobrowski]
        NAPTR   = 35,    // Naming Authority Pointer      [RFC2168, RFC2915]
        KX      = 36,    // Key Exchanger                          [RFC2230]
        CERT    = 37,    // CERT                                   [RFC2538]
        A6      = 38,    // A6                                     [RFC2874]
        DNAME   = 39,    // DNAME                                  [RFC2672]
        SINK    = 40,    // SINK                                   [Eastlake]
        OPT     = 41,    // OPT                                    [RFC2671]
        APL     = 42,    // APL                                    [RFC3123]
        DS      = 43,    // Delegation Signer                      [RFC3658]
        SSHFP   = 44,    // SSH Key Fingerprint  [RFC-ietf-secsh-dns-05.txt]
        RRSIG   = 46,    // RRSIG                                  [RFC3755]
        NSEC    = 47,    // NSEC                                   [RFC3755]
        DNSKEY  = 48,    // DNSKEY                                 [RFC3755]
        UINFO   = 100,   //                                  [IANA-Reserved]
        UID     = 101,   //                                  [IANA-Reserved]
        GID     = 102,   //                                  [IANA-Reserved]
        UNSPEC  = 103,   //                                  [IANA-Reserved]
        TKEY    = 249,   // Transaction Key                        [RFC2930]
        TSIG    = 250,   // Transaction Signature                  [RFC2845]
        IXFR    = 251,   // incremental transfer                   [RFC1995]
        AXFR    = 252,   // transfer of an entire zone             [RFC1035]
        MAILB   = 253,   // mailbox-related RRs (MB, MG or MR)     [RFC1035]
        MAILA   = 254,   // mail agent RRs (Obsolete - see MX)     [RFC1035]
        ALL     = 255,   // A request for all records              [RFC1035]
    }

    public enum OpCode : byte
    {
        Query  = 0,      //                                        [RFC1035]
        // IQUERY  = 1   //  OpCode Retired                        [RFC3425]
        Status = 2,      //                                        [RFC1035]
        // 3             // reserved                               [IANA]
        Notify = 4,      //                                        [RFC1996]
        Update = 5,      //                                        [RFC2136]
        // 6-15 available for assignment
    }

    public enum RCode : ushort
    {
        NoError          = 0,   // No Error                           [RFC1035]
        FormErr          = 1,   // Format Error                       [RFC1035]
        ServFail         = 2,   // Server Failure                     [RFC1035]
        NXDomain         = 3,   // Non-Existent Domain                [RFC1035]
        NotImp           = 4,   // Not Implemented                    [RFC1035]
        Refused          = 5,   // Query Refused                      [RFC1035]
        YXDomain         = 6,   // Name Exists when it should not     [RFC2136]
        YXRRSet          = 7,   // RR Set Exists when it should not   [RFC2136]
        NXRRSet          = 8,   // RR Set that should exist does not  [RFC2136]
        NotAuth          = 9,   // Server Not Authoritative for zone  [RFC2136]
        NotZone          = 10,  // Name not contained in zone         [RFC2136]
        Max4BitCode      = NotZone,
        //               11-15,    Available for assignment
        BADVERS          = 16,  // Bad OPT Version                    [RFC2671]
        BADSIG           = 16,  // TSIG Signature Failure             [RFC2845]
        BADKEY           = 17,  // Key not recognized                 [RFC2845]
        BADTIME          = 18,  // Signature out of time window       [RFC2845]
        BADMODE          = 19,  // Bad TKEY Mode                      [RFC2930]
        BADNAME          = 20,  // Duplicate key name                 [RFC2930]
        BADALG           = 21,  // Algorithm not supported            [RFC2930]
        // 22-3840              available for assignment
        //  0x0016-0x0F00
        // 3841-4095            Private Use
        //  0x0F01-0x0FFF
        // 4096-65535           available for assignment
        //  0x1000-0xFFFF
    }

    public enum Flags : ushort
    {
        NONE = 0,
        QR   = 0x8000, // Response (1) vs Query (0)
        AA   = 0x0400, // Authoritative (1) vs Non-authoritative (0)
        TC   = 0x0200, // Truncated
        RD   = 0x0100, // Recursion Desired
        RA   = 0x0080, // Recursion Available
        MBZ  = 0x0040, // Must-Be-Zero
        AD   = 0x0020, // Authenticated data (DNSSEC)
        CD   = 0x0010, // Checking Disabled  (DNSSEC)
        ALL  = 0x87f0, // All bit-field bits
    }

    /// <summary>
    /// Convert between textual and binary DNS names.
    /// </summary>
    ///
    /// <remarks>
    /// <para>
    /// RFC1035 describes how names should be packed in DNS
    /// queries and responses.  The method is described as:
    /// </para>
    /// <para>
    /// Domain names in messages are expressed in terms of a
    /// sequence of labels.  Each label is represented as a one
    /// octet length field followed by that number of octets.
    /// Since every domain name ends with the null label of the
    /// root, a domain name is terminated by a length byte of
    /// zero.  The high order two bits of every length octet
    /// must be zero, and the remaining six bits of the length
    /// field limit the label to 63 octets or less.
    /// </para>
    /// </remarks>
    public class LabelEncoding
    {
        private static ASCIIEncoding ascii = new ASCIIEncoding();

        private LabelEncoding() {}

        static public byte[] GetBytes(string s)
        {
            byte[] result = new byte[GetByteCount(s)];
            PutBytes(s, result, 0);
            return result;
        }

        public static int PutBytes(string input,
                                   byte[] bytes,
                                   int     byteIndex)
        {
            if (input.Length == 0) {
                bytes[byteIndex] = 0;
                return 1;
            }

            ascii.GetBytes(input, 0, input.Length, bytes, byteIndex + 1);
            int outIndex = byteIndex;
            int finalIndex = byteIndex + input.Length + 1;
            bytes[finalIndex] = 0;

            for (int i = byteIndex + 1; i <= finalIndex; i++) {
                if (bytes[i] == (byte)'.' || bytes[i] == 0) {
                    int blockLength = i - outIndex - 1;
                    if (blockLength > Format.MaxLabelLength)
                        throw new ArgumentException();
                    bytes[outIndex] = (byte)(i - outIndex - 1);
                    outIndex = i++;
                }
            }
            return finalIndex + 1 - byteIndex;
        }

        static public int GetByteCount(string s)
        {
            return (s.Length > 0) ? (2 + s.Length) : 1;
        }

        /// <summary>
        /// Convert name from sequence of bytes to string.
        /// </summary>
        ///
        /// <returns>
        /// Returns number of bytes consumed, or 0 if input is invalid.
        ///</returns>
        public static int GetString(byte[]     bytes,
                                    int         byteIndex,
                                    out string  output)
        {
            int startIndex = byteIndex;

            if (bytes[byteIndex] == 0)
                goto fail;

            // Validation and copy to mutable buffer pass
            while (bytes[byteIndex] != 0) {
                if (byteIndex - startIndex - 1 > Format.MaxNameLength)
                    goto fail;

                int offset = (int) bytes[byteIndex];
                if ((offset & 0xc0) != 0)
                    goto fail;

                int newByteIndex = byteIndex + offset + 1;
                if (newByteIndex > bytes.Length)
                    goto fail;
                byteIndex = newByteIndex;
            }

            // Copy data into a local buffer.  At first glance,
            // you might realize the unpacking could be done in
            // place.  However, because of RFC1035 name
            // compression some other block may point to the raw
            // data in the packet and expect it to be in packed
            // format.
            byte [] workBytes = new byte [byteIndex + 1 - startIndex];
            Array.Copy(bytes, startIndex, workBytes, 0, workBytes.Length);

            // Modify length bytes to '.' chars
            int workIndex = 0;
            while (workBytes[workIndex] != 0) {
                byte offset = workBytes[workIndex];
                workBytes[workIndex] = (byte)'.';
                workIndex += (int)offset + 1;
            }
            Debug.Assert(workIndex + 1 == workBytes.Length);
            output = ascii.GetString(workBytes, 1, workIndex - 1);

            return workBytes.Length;

          fail:
            output = "";
            return 0;
        }
    }

    public class InvalidDnsFormatException : SystemException
    {
        public InvalidDnsFormatException(String message)
            : base(message)
        {
        }

        public InvalidDnsFormatException(String message,
                                         Exception innerException)
            : base(message, innerException)
        {
        }

        public InvalidDnsFormatException(String format, params object [] args)
            : base (String.Format(format, args))
        {
        }
    }

    public class Query
    {
        public readonly string Name;
        public readonly Type   Type;
        public readonly Class  Class;

        public Query(string queryName, Type queryType, Class queryClass)
        {
            if (queryName == null)
                throw new ArgumentNullException("queryName");

            this.Name  = queryName;
            this.Type  = queryType;
            this.Class = queryClass;
        }

        public int Size
        {
            // Packed name size plus 2 bytes Type, 2 bytes Class
            get { return LabelEncoding.GetByteCount(Name) + 4; }
        }

        public int Write(byte[] buffer, ref int offset)
        {
            offset += LabelEncoding.PutBytes(Name, buffer, offset);
            offset += NetworkBitConverter.PutBytes((ushort)Type,
                                                   buffer, offset);
            offset += NetworkBitConverter.PutBytes((ushort)Class,
                                                   buffer, offset);
            return offset;
        }

        public static Query Parse(byte [] buffer, ref int offset)
        {
            string name;

            int used = LabelEncoding.GetString(buffer, offset, out name);
            if (used == 0)
                throw new InvalidDnsFormatException("name");
            offset += used;

            ushort qType = NetworkBitConverter.ToUInt16(buffer, offset);
            offset += 2;

            ushort qClass = NetworkBitConverter.ToUInt16(buffer, offset);
            offset += 2;

            return new Query(name, (Type) qType, (Class) qClass);
        }

        public static bool operator == (Query lhs, Query rhs)
        {
            if (lhs == null && rhs == null) return true;
            if (lhs == null) return false;
            if (rhs == null) return false;
            return (lhs.Name  == rhs.Name &&
                    lhs.Type  == rhs.Type &&
                    lhs.Class == rhs.Class);
        }

        public static bool operator != (Query lhs, Query rhs)
        {
            return !(lhs == rhs);
        }

        public override bool Equals(Object other)
        {
            Query query = other as Query;
            return ((Object.ReferenceEquals(query, null) == false) &&
                    (this == query));
        }

        public override int GetHashCode()
        {
            return this.Name.GetHashCode() ^ ((int)Type << 16) ^ (int)Class;
        }
    }

    public class ResourceRecord
    {
        public readonly string   Name;
        public readonly Type     Type;
        public readonly Class    Class;
        public readonly uint     TtlSeconds;
        public readonly byte[]   RData;

        public ResourceRecord(string name,
                              Type   recordType,
                              Class  recordClass,
                              uint   ttlSeconds,
                              byte[] rdata)
        {
            if (name == null)
                throw new ArgumentNullException("name");

            this.Name       = name;
            this.Type       = recordType;
            this.Class      = recordClass;
            this.TtlSeconds = ttlSeconds;
            this.RData      = rdata;
        }

        public int Size
        {
            get {
                int baseLength = LabelEncoding.GetByteCount(Name) + 10;
                if (RData == null)
                    return baseLength;
                return baseLength + RData.Length;
            }
        }

        public int Write(byte [] buffer, ref int offset)
        {
            offset += LabelEncoding.PutBytes(Name, buffer, offset);
            offset += NetworkBitConverter.PutBytes((ushort) Type,
                                                   buffer, offset);
            offset += NetworkBitConverter.PutBytes((ushort) Class,
                                                    buffer, offset);
            offset += NetworkBitConverter.PutBytes(TtlSeconds, buffer, offset);

            if (RData == null) {
                offset += NetworkBitConverter.PutBytes((ushort)0,
                                                        buffer, offset);
            }
            else {
                offset += NetworkBitConverter.PutBytes((ushort)RData.Length,
                                                        buffer, offset);
                Buffer.MoveMemory(buffer, RData, offset, 0, RData.Length);
                offset += RData.Length;
            }
            return offset;
        }

        public static ResourceRecord Parse(byte [] buffer, ref int offset)
        {
            string name;
            if ((buffer[offset] & 0xc0) == 0xc0) {
                // Detected compression.  Name is at offset in
                // lower 14 bits of next 2 bytes.
                int start = NetworkBitConverter.ToInt16(buffer, offset);
                if (LabelEncoding.GetString(buffer, start & 0x3fff,
                                            out name) == 0)
                    throw new InvalidDnsFormatException("name");
                offset += 2;
            }
            else {
                int used = LabelEncoding.GetString(buffer, offset, out name);
                if (used == 0)
                    throw new InvalidDnsFormatException("name");
                offset += used;
            }

            ushort rType = NetworkBitConverter.ToUInt16(buffer, offset);
            offset += 2;

            ushort rClass = NetworkBitConverter.ToUInt16(buffer, offset);
            offset += 2;

            uint ttlSeconds = NetworkBitConverter.ToUInt32(buffer, offset);
            offset += 4;

            ushort rdataLength = NetworkBitConverter.ToUInt16(buffer, offset);
            offset += 2;

            byte [] rdata = new byte[rdataLength];
            Array.Copy(buffer, offset, rdata, 0, rdataLength);
            offset += rdataLength;

            return new ResourceRecord(name, (Type) rType, (Class) rClass,
                                      ttlSeconds, rdata);
        }

        public static bool operator == (ResourceRecord lhs, ResourceRecord rhs)
        {
            if (lhs == null && rhs == null) return true;
            if (lhs == null) return false;
            if (rhs == null) return false;

            if (lhs.Name != rhs.Name || lhs.Type != rhs.Type ||
                lhs.Class != rhs.Class || lhs.TtlSeconds != rhs.TtlSeconds)
                return false;
            if (lhs.RData == null)
                return rhs.RData == null;
            if (rhs.RData == null)
                return false;
            if (lhs.RData.Length != rhs.RData.Length)
                return false;
            for (int i = 0; i < lhs.RData.Length; i++)
                if (lhs.RData[i] != rhs.RData[i])
                    return false;
            return true;
        }

        public static bool operator != (ResourceRecord lhs, ResourceRecord rhs)
        {
            return !(lhs == rhs);
        }

        public override bool Equals(Object other)
        {
            ResourceRecord rr = other as ResourceRecord;
            return ((Object.ReferenceEquals(rr, null) == false) &&
                    (rr == this));
        }

        public override int GetHashCode()
        {
            int hashCode = this.Name.GetHashCode();
            hashCode ^= (int)Type << 16;
            hashCode ^= (int)Class;
            if (RData != null) {
                hashCode ^= RData.Length;
                for (int i = 0; i < RData.Length; i ++) {
                    hashCode = hashCode ^ (hashCode << 1);
                    hashCode += (int)RData[i];
                }
            }
            return hashCode;
        }
    }

    public class Format
    {
        public const ushort ServerPort = 53;

        public const int MaxLabelLength      = 63;
        public const int MinLabelLength      =  1;
        public const int MaxNameLength       = 255;
        public const int MaxUdpMessageLength = 512;

        private const int OpCodeRoll = 11;
        private const int OpCodeMask = 0x0f;
        private const int RCodeMask  = 0x0f;

        private ushort     id;
        private Flags      flags;
        private OpCode     opCode;
        private RCode      rCode;
        private ArrayList queries;
        private ArrayList answerRRs;
        private ArrayList authorityRRs;
        private ArrayList additionalRRs;

        private static ushort nextId = 0;

        public Format(ushort id, Flags flags, OpCode opCode, RCode rCode)
        {
            this.id            = id;
            this.queries       = new ArrayList();
            this.answerRRs     = new ArrayList();
            this.authorityRRs  = new ArrayList();
            this.additionalRRs = new ArrayList();
            this.SetFlags(flags);
            this.SetOpCode(opCode);
            this.SetRCode(rCode);
        }

        public Format()
            : this (++nextId, Flags.NONE, OpCode.Query, RCode.NoError)
        {
        }

        public Flags GetFlags()
        {
            return flags;
        }

        public void SetFlags(Flags newFlags)
        {
            if ((newFlags & Flags.ALL) != newFlags)
                throw new ArgumentException("Invalid flags present");
            flags = newFlags;
        }

        public OpCode GetOpCode()
        {
            return opCode;
        }

        public void SetOpCode(OpCode newOpCode)
        {
            switch (newOpCode) {
                case OpCode.Query:  break;
                case OpCode.Status: break;
                case OpCode.Notify: break;
                case OpCode.Update: break;
                default:
                    throw new ArgumentException("Invalid OpCode");
            }
            opCode = newOpCode;
        }

        public RCode GetRCode()
        {
            return rCode;
        }

        public void SetRCode(RCode newRCode)
        {
            if (newRCode > RCode.Max4BitCode)
                throw new ArgumentException("Invalid RCode");
            rCode = newRCode;
        }

        public ArrayList Queries
        {
            get { return queries; }
        }

        public ArrayList AnswerRRs
        {
            get { return answerRRs; }
        }

        public ArrayList AuthorityRRs
        {
            get { return authorityRRs; }
        }

        public ArrayList AdditionalRRs
        {
            get { return additionalRRs; }
        }

        public int Size
        {
            get
            {
                int total = 12; // Fixed component
                foreach (Query q in queries)
                    total += q.Size;
                foreach (ResourceRecord r in answerRRs)
                    total += r.Size;
                foreach (ResourceRecord r in authorityRRs)
                    total += r.Size;
                foreach (ResourceRecord r in additionalRRs)
                    total += r.Size;
                return total;
            }
        }

        private void Write(byte[] buffer, ushort value, ref int offset)
        {
            buffer[offset++] = (byte)((int)value >> 8);
            buffer[offset++] = (byte)((int)value & 0xff);
        }

        public int Write(byte[] buffer, ref int offset)
        {
            Debug.Assert((((int)opCode << OpCodeRoll) & (int)Flags.ALL) == 0);
            Debug.Assert((((int)rCode) & (int)Flags.ALL) == 0);

            Write(buffer, id, ref offset);

            int word2 = ((int)opCode << OpCodeRoll) | (int)flags | (int)rCode;
            Write(buffer, (ushort) word2, ref offset);

            Write(buffer, (ushort) queries.Count, ref offset);
            Write(buffer, (ushort) answerRRs.Count, ref offset);
            Write(buffer, (ushort) authorityRRs.Count, ref offset);
            Write(buffer, (ushort) additionalRRs.Count, ref offset);

            foreach (Query q in queries)
                q.Write(buffer, ref offset);
            foreach (ResourceRecord r in answerRRs)
                r.Write(buffer, ref offset);
            foreach (ResourceRecord r in authorityRRs)
                r.Write(buffer, ref offset);
            foreach (ResourceRecord r in additionalRRs)
                r.Write(buffer, ref offset);

            return offset;
        }

        public static Format Parse(byte [] buffer, ref int offset)
        {
            //
            // First extract enough information to instantiate a Dns.Format
            //
            ushort id = NetworkBitConverter.ToUInt16(buffer, offset);
            offset += 2;

            ushort flagsAndCodes = NetworkBitConverter.ToUInt16(buffer,
                                                                offset);
            offset += 2;

            Flags flags = (Flags)((int)flagsAndCodes & (int)Flags.ALL);

            OpCode opCode =
                (OpCode)(((int)flagsAndCodes >> OpCodeRoll) & OpCodeMask);

            RCode rCode = (RCode)((int)flagsAndCodes & RCodeMask);

            //
            // Instantiate Dns.Format
            //
            Format format = new Format(id, flags, opCode, rCode);

            //
            // Extract query and record counts and then instantiate
            // Query and ResourceRecord objects
            //

            ushort totalQueries = NetworkBitConverter.ToUInt16(buffer,
                                                               offset);
            offset += 2;

            ushort totalAnswerRRs = NetworkBitConverter.ToUInt16(buffer,
                                                                 offset);
            offset += 2;

            ushort totalAuthorityRRs = NetworkBitConverter.ToUInt16(buffer,
                                                                    offset);
            offset += 2;

            ushort totalAdditionalRRs =  NetworkBitConverter.ToUInt16(buffer,
                                                                      offset);
            offset += 2;

            for (ushort i = 0; i < totalQueries; i++) {
                Query query = Query.Parse(buffer, ref offset);
                format.queries.Add(query);
            }

            // XXX Parsing stops here when a query fails.
            //
            // When a query fails, servers sometimes
            // indicate resource records are present, but the
            // data that we'd expect to be a resource record
            // does not match the format defined in
            // RFC1035. Details may exist in another RFC (???).
            if (rCode != RCode.NoError)
                return format;

            for (ushort i = 0; i < totalAnswerRRs; i++) {
                ResourceRecord rr = ResourceRecord.Parse(buffer, ref offset);
                format.answerRRs.Add(rr);
            }

            for (ushort i = 0; i < totalAuthorityRRs; i++) {
                ResourceRecord rr = ResourceRecord.Parse(buffer, ref offset);
                format.authorityRRs.Add(rr);
            }

            for (ushort i = 0; i < totalAdditionalRRs; i++) {
                ResourceRecord rr = ResourceRecord.Parse(buffer, ref offset);
                format.additionalRRs.Add(rr);
            }

            return format;
        }

        private static bool ListsEqual(ArrayList lhs, ArrayList rhs)
        {
            if (lhs == null && rhs == null)
                return true;

            if (lhs == null)
                return false;

            if (rhs == null)
                return false;

            if (lhs.Count != rhs.Count)
                return false;

            for (int i = 0; i < lhs.Count; i++)
                if (Object.Equals(lhs[i],rhs[i]) == false)
                    return false;

            return true;
        }

        public static bool operator == (Format lhs, Format rhs)
        {
            if (lhs == null && rhs == null) return true;
            if (lhs == null) return false;
            if (rhs == null) return false;
            if (lhs.id     != rhs.id     || lhs.flags  != rhs.flags  ||
                lhs.opCode != rhs.opCode || lhs.rCode  != rhs.rCode)
                return false;

            return (ListsEqual(lhs.queries, rhs.queries)             &&
                    ListsEqual(lhs.answerRRs, rhs.answerRRs)         &&
                    ListsEqual(lhs.additionalRRs, rhs.additionalRRs) &&
                    ListsEqual(lhs.authorityRRs, rhs.authorityRRs));
        }

        public static bool operator != (Format lhs, Format rhs)
        {
            return !(lhs == rhs);
        }

        public override bool Equals(Object other)
        {
            Format format = other as Format;
            return ((Object.ReferenceEquals(format, null) == false)
                    && (format == this));
        }

        private static int GetListHashCode(ArrayList list, int nullHash)
        {
            if (list == null)
                return nullHash;

            int hashCode = ~nullHash;
            foreach (object o in list) {
                hashCode = hashCode ^ o.GetHashCode();
                hashCode = hashCode ^ (hashCode << 1);
            }
            return hashCode;
        }

        public override int GetHashCode()
        {
            int hashCode = (int)id << 16;
            hashCode += ((int)opCode << OpCodeRoll) | (int)flags | (int)rCode;
            hashCode ^= GetListHashCode(queries, 0x01233210);
            hashCode ^= GetListHashCode(answerRRs, 0x17017017);
            hashCode ^= GetListHashCode(authorityRRs, 0x22223333);
            hashCode ^= GetListHashCode(additionalRRs, 0x41414141);
            return hashCode;
        }

        private static bool IsSafeLabel(string name, int begin, int end)
        {
            Debug.Assert(end > begin);

            if (end - begin > Format.MaxLabelLength ||
                end - begin < Format.MinLabelLength)
                return false;

            // The description in RFC 1035 section 2.1 prefers
            // first char to be [A-z], however this would rule out
            // entries in the IN-ADDR.ARPA domain used to lookup
            // hostnames from IP addresses.
            if (Char.IsLetterOrDigit(name[begin]) == false)
                return false;

            // Last char [A-z0-9]
            int last = end - 1;
            if (Char.IsLetterOrDigit(name[last]) == false)
                return false;

            for (int i = begin + 1; i < last; i++) {
                // Middle Chars [A-z0-9-]
                if (Char.IsLetterOrDigit(name[i]) == false &&
                    name[i] != '-')
                    return false;
            }
            return true;
        }

        public static bool IsSafeDnsName(string name)
        {
            //
            // Grammar from RFC1035:
            //
            //   <domain> ::= <subdomain> | " "
            //
            //   <subdomain> ::= <label> | <subdomain> "." <label>
            //
            //   <label> ::= <letter> [ [ <ldh-str> ] <let-dig> ]
            //
            //   <ldh-str> ::= <let-dig-hyp> | <let-dig-hyp> <ldh-str>
            //
            //   <let-dig-hyp> ::= <let-dig> | "-"
            //
            //   <let-dig> ::= <letter> | <digit>
            //
            if (name.Length > Format.MaxNameLength)
                return false;

            int labelStart = 0;
            do
            {
                int labelEnd = name.IndexOf('.', labelStart);
                if (labelEnd < 0) {
                    return IsSafeLabel(name, labelStart, name.Length);
                }
                if (IsSafeLabel(name, labelStart, labelEnd) == false) {
                    return false;
                }
                labelStart = labelEnd + 1;
            } while (labelStart < name.Length);

            return false;
        }
    }
}

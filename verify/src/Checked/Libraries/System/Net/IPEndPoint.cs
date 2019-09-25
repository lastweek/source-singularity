////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

namespace System.Net
{
    using System.Net.Sockets;
    using System.Globalization;

    /// <devdoc>
    ///    <para>
    ///       Provides an IP address.
    ///    </para>
    /// </devdoc>
    public class IPEndPoint : EndPoint {
        /// <devdoc>
        ///    <para>
        ///       Specifies the minimum acceptable value for the <see cref='System.Net.IPEndPoint.Port'/>
        ///       property.
        ///    </para>
        /// </devdoc>
        public const int MinPort = 0x00000000;
        /// <devdoc>
        ///    <para>
        ///       Specifies the maximum acceptable value for the <see cref='System.Net.IPEndPoint.Port'/>
        ///       property.
        ///    </para>
        /// </devdoc>
        public const int MaxPort = 0x0000FFFF;

        private IPAddress m_Address;
        private int m_Port;
        private const int IPv4AddressSize = 16;

        internal const int AnyPort = MinPort;

        internal static IPEndPoint Any     = new IPEndPoint(IPAddress.Any, AnyPort);


        public override AddressFamily AddressFamily {
            get {
                return m_Address.AddressFamily;
            }
        }

        /// <devdoc>
        ///    <para>Creates a new instance of the IPEndPoint class with the specified address and
        ///       port.</para>
        /// </devdoc>
        public IPEndPoint(long address, int port) {
            if (!ValidationHelper.ValidateTcpPort(port)) {
                throw new ArgumentOutOfRangeException("port");
            }
            m_Port = port;
            m_Address = new IPAddress(address);
        }

        /// <devdoc>
        ///    <para>Creates a new instance of the IPEndPoint class with the specified address and port.</para>
        /// </devdoc>
        public IPEndPoint(IPAddress address, int port) {
            if (address == null) {
                throw new ArgumentNullException("address");
            }
            if (!ValidationHelper.ValidateTcpPort(port)) {
                throw new ArgumentOutOfRangeException("port");
            }
            m_Port = port;
            m_Address = address;
        }

        /// <devdoc>
        ///    <para>
        ///       Gets or sets the IP address.
        ///    </para>
        /// </devdoc>
        public IPAddress Address {
            get {
                return m_Address;
            }
            set {
                m_Address = value;
            }
        }

        /// <devdoc>
        ///    <para>
        ///       Gets or sets the port.
        ///    </para>
        /// </devdoc>
        public int Port {
            get {
                return m_Port;
            }
            set {
                if (!ValidationHelper.ValidateTcpPort(value)) {
                    throw new ArgumentOutOfRangeException("value");
                }
                m_Port = value;
            }
        }

        public override string ToString() {
            return Address.ToString() + ":" + Port.ToString();
        }

        public override SocketAddress Serialize() {
            //
            // create a new SocketAddress
            //
            SocketAddress socketAddress = new SocketAddress(m_Address.AddressFamily, IPv4AddressSize);

            //
            // populate it
            //
            socketAddress[2] = unchecked((byte)(this.Port>> 8));
            socketAddress[3] = unchecked((byte)(this.Port    ));

            uint address = (uint)Address.m_addr;
            socketAddress[4] = unchecked((byte)(address    ));
            socketAddress[5] = unchecked((byte)(address>> 8));
            socketAddress[6] = unchecked((byte)(address>>16));
            socketAddress[7] = unchecked((byte)(address>>24));

            //
            // return it
            //
            return socketAddress;
        }

        public override EndPoint Create(SocketAddress socketAddress) {
            //
            // validate SocketAddress
            //
            if (socketAddress.Family != this.AddressFamily) {
                throw new ArgumentException("Mismatched address family");
            }

            if (socketAddress.Size < 8) {
                throw new ArgumentException("Socket Address size too small");
            }

            // HACKHACK: we don't support v6 in Singularity
            if (this.AddressFamily == AddressFamily.InterNetworkV6) {
                throw new NotSupportedException();
            }
            else {
                //
                // strip out of SocketAddress information on the EndPoint
                //
                int port = (int)(
                        (socketAddress[2]<<8 & 0xFF00) |
                        (socketAddress[3])
                        );

                long address = (long)(
                        (socketAddress[4]     & 0x000000FF) |
                        (socketAddress[5]<<8  & 0x0000FF00) |
                        (socketAddress[6]<<16 & 0x00FF0000) |
                        (socketAddress[7]<<24)
                        ) & 0x00000000FFFFFFFF;

                IPEndPoint created = new IPEndPoint(address, port);

                //
                // return it
                //
                return created;
            }
        }


        //UEUE
        public override bool Equals(object comparand) {
            if (!(comparand is IPEndPoint)) {
                return false;
            }
            return ((IPEndPoint)comparand).m_Address.Equals(m_Address) && ((IPEndPoint)comparand).m_Port==m_Port;
        }

        //UEUE
        public override int GetHashCode() {
            return m_Address.GetHashCode() ^ m_Port;
        }


    }; // class IPEndPoint


} // namespace System.Net



//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IPv4Network.cs
//

using System;

namespace System.Net.IP
{
    /// <summary>
    /// IPv4 Network Structure.
    /// </summary>
    [ CLSCompliant(false) ]
    public struct IPv4Network
    {
        private IPv4 ipNetwork;
        private int maskLength;

        public IPv4Network(IPv4 ipNetwork, int maskLength)
        {
            if (maskLength < 0 || maskLength > IPv4.BitCount) {
                throw new ArgumentException();
            }
            this.maskLength = maskLength;
            this.ipNetwork  = ipNetwork & IPv4.NetMask(maskLength);
        }

        public IPv4Network(IPv4 networkAddress, IPv4 networkMask)
        {
            this.maskLength = IPv4.GetMaskLength(networkMask);
            this.ipNetwork  = networkAddress & IPv4.NetMask(this.maskLength);
        }

        public IPv4 Network
        {
            get { return ipNetwork; }
        }

        public int MaskLength
        {
            get { return maskLength; }
        }

        public IPv4 NetMask
        {
            get { return IPv4.NetMask(maskLength); }
        }

        public IPv4 LowerBound
        {
            get { return ipNetwork; }
        }

        public IPv4 UpperBound
        {
            get { return ipNetwork | ~NetMask; }
        }

        public bool IsMoreSpecificThan(IPv4Network other)
        {
            return maskLength > other.maskLength;
        }

        public bool IsLessSpecificThan(IPv4Network other)
        {
            return maskLength < other.maskLength;
        }

        public bool Contains(IPv4Network network)
        {
            return ( (maskLength <= network.maskLength) &&
                     ((network.ipNetwork & this.NetMask) == this.ipNetwork) );
        }

        public bool Contains(IPv4 ipAddress)
        {
            return (ipAddress & this.NetMask) == this.ipNetwork;
        }

        public static bool operator == (IPv4Network x, IPv4Network y)
        {
            return ( (x.maskLength == y.maskLength) &&
                     (x.ipNetwork  == y.ipNetwork) );
        }

        public static bool operator < (IPv4Network x, IPv4Network y)
        {
            if (x.maskLength == y.maskLength) {
                return x.ipNetwork < y.ipNetwork;
            }
            return x.maskLength < y.maskLength;
        }

        public static bool operator <= (IPv4Network x, IPv4Network y)
        {
            if (x.maskLength == y.maskLength) {
                return x.ipNetwork <= y.ipNetwork;
            }
            return x.maskLength <= y.maskLength;
        }

        public static bool operator != (IPv4Network x, IPv4Network y)
        {
            return !(x == y);
        }

        public static bool operator > (IPv4Network x, IPv4Network y)
        {
            return !(x <= y);
        }

        public static bool operator >= (IPv4Network x, IPv4Network y)
        {
            return !(x < y);
        }

        public override string! ToString()
        {
            return String.Format("{0}/{1}", ipNetwork, maskLength);
        }

        /// <summary>
        ///
        /// Parse an IPv4 network string representation into an IPv4Network.
        ///
        /// <para> The representation should either be <ipAddress/> or
        ///        <ipAddress/>/<masklength/>.
        /// </para>
        ///
        /// <para> Example forms of IPv4 Networks are: 10.0.2.0/24,
        ///        10.0.0.1.
        /// </para>
        ///
        /// </summary>
        ///
        /// <exception cref="ArgumentNullException"></exception>
        ///
        /// <exception cref="FormatException">
        /// Thrown when IP address component of format is invalid or too many
        /// slashes appear in string argument, or netmask length is not a valid
        /// integer.
        /// </exception>
        ///
        /// <exception cref="ArgumentException">
        /// Thrown when specified mask length is greater than
        /// <c>IPv4.BitCount</c>or less than zero.
        /// </exception>
        ///
        /// <exception cref="OverflowException">
        /// Netmask length overflows valid values for integers
        /// </exception>
        ///
        public static IPv4Network Parse(string ipNetwork)
        {
            if (ipNetwork == null)
                throw new ArgumentNullException("ipNetwork");

            string [] pieces = ipNetwork.Split('/');

            if (pieces.Length > 2)
                throw new FormatException("slash overload");

            int maskLength = IPv4.BitCount;
            if (pieces.Length == 2)
                maskLength = Int32.Parse(pieces[1]);

            return new IPv4Network(IPv4.Parse(pieces[0]), maskLength);
        }

        /// <summary>
        /// Exception-lite IPv4 network address parser.
        /// </summary>
        ///
        /// <returns><c>true</c> on success, <c>false</c> if supplied address
        /// is not a valid IPv4 string representation.
        /// </returns>
        ///
        /// <exception cref = "ArgumentNullException"></exception>
        ///
        public static bool Parse(string ipNetwork, out IPv4Network network)
        {
            try {
                network = Parse(ipNetwork);
                return true;
            }
            catch (ArgumentException) {

            }
            catch (FormatException) {

            }
            catch (OverflowException) {

            }

            network = Default;
            return false;
        }

        public override int GetHashCode()
        {
            return ipNetwork.GetHashCode() ^ (int)maskLength;
        }

        public override bool Equals(object other)
        {
            if (other is IPv4Network) {
                return (this == (IPv4Network)other);
            }
            return false;
        }

        public static readonly IPv4Network Default =
            new IPv4Network(IPv4.Zero, 0);

        public static readonly IPv4Network Loopback =
            new IPv4Network(IPv4.Loopback, 8);
    } // struct IPv4Network
} // namespace System.Net.IP

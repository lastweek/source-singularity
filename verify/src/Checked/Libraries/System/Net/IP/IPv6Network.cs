///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;

namespace System.Net.IP
{
    /// <summary>
    /// IPv6 Network Structure.
    /// </summary>
    [ CLSCompliant(false) ]
    public class IPv6Network
    {
        private IPv6 ipNetwork;
        private int maskLength;

        public IPv6Network(IPv6 ipNetwork, int maskLength)
        {
            if (maskLength < 0 || maskLength > IPv6.BitCount) {
                throw new ArgumentException();
            }
            this.maskLength = maskLength;
            this.ipNetwork  = ipNetwork & IPv6.NetMask(maskLength);
        }

        public IPv6Network(IPv6 networkAddress, IPv6 networkMask)
        {
            this.maskLength = IPv6.GetMaskLength(networkMask);
            this.ipNetwork  = networkAddress & IPv6.NetMask(this.maskLength);
        }

        public IPv6 Network
        {
            get { return ipNetwork; }
        }

        public int MaskLength
        {
            get { return maskLength; }
        }

        public IPv6 NetMask
        {
            get { return IPv6.NetMask(maskLength); }
        }

        public IPv6 LowerBound
        {
            get { return ipNetwork; }
        }

        public IPv6 UpperBound
        {
            get { return ipNetwork | ~NetMask; }
        }

        public bool IsMoreSpecificThan(IPv6Network other)
        {
            return maskLength > other.maskLength;
        }

        public bool IsLessSpecificThan(IPv6Network other)
        {
            return maskLength < other.maskLength;
        }

        public bool Contains(IPv6Network network)
        {
            return ( (maskLength <= network.maskLength) &&
                     ((network.ipNetwork & this.NetMask) == this.ipNetwork) );
        }

        public bool Contains(IPv6 ipAddress)
        {
            return (ipAddress & this.NetMask) == this.ipNetwork;
        }

        public static bool operator ==(IPv6Network x, IPv6Network y)
        {
            return ( (x.maskLength == y.maskLength) &&
                     (x.ipNetwork  == y.ipNetwork) );
        }

        public static bool operator <(IPv6Network x, IPv6Network y)
        {
            if (x.maskLength == y.maskLength) {
                return x.ipNetwork < y.ipNetwork;
            }
            return x.maskLength < y.maskLength;
        }

        public static bool operator <=(IPv6Network x, IPv6Network y)
        {
            if (x.maskLength == y.maskLength) {
                return x.ipNetwork <= y.ipNetwork;
            }
            return x.maskLength <= y.maskLength;
        }

        public static bool operator !=(IPv6Network x, IPv6Network y)
        {
            return !(x == y);
        }

        public static bool operator >(IPv6Network x, IPv6Network y)
        {
            return !(x <= y);
        }

        public static bool operator >=(IPv6Network x, IPv6Network y)
        {
            return !(x < y);
        }

        public override string ToString()
        {
            return String.Format("{0}/{1}", ipNetwork, maskLength);
        }

        public override int GetHashCode()
        {
            return ipNetwork.GetHashCode() ^ (int)maskLength;
        }

        public override bool Equals(object other)
        {
            if (other is IPv6Network) {
                return (this == (IPv6Network)other);
            }
            return false;
        }

        /// <summary>
        ///
        /// Parse an IPv6 network string representation into an IPv6Network.
        ///
        /// <para> The representation should either be <ipAddress/> or
        ///        <ipAddress/>/<masklength/>.
        /// </para>
        ///
        /// <para> Example forms of IPv6 Networks are: 10.0.2.0/24,
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
        /// <c>IPv6.BitCount</c> or less than zero.
        /// </exception>
        ///
        /// <exception cref="OverflowException">
        /// Netmask length overflows valid values for integers
        /// </exception>
        ///
        public static IPv6Network Parse(string ipNetwork)
        {
            if (ipNetwork == null)
                throw new ArgumentNullException("ipNetwork");

            string [] pieces = ipNetwork.Split('/');

            if (pieces.Length > 2)
                throw new FormatException("slash overload");

            int maskLength = IPv6.BitCount;
            if (pieces.Length == 2)
                maskLength = Int32.Parse(pieces[1]);

            return new IPv6Network(IPv6.Parse(pieces[0]), maskLength);
        }

        /// <summary>
        /// Exception-lite IPv6 network address parser.
        /// </summary>
        ///
        /// <returns><c>true</c> on success, <c>false</c> if supplied address
        /// is not a valid IPv6 string representation.
        /// </returns>
        ///
        /// <exception cref = "ArgumentNullException"></exception>
        ///
        public static bool Parse(string ipNetwork, out IPv6Network network)
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


        public static readonly IPv6Network Default =
                                                new IPv6Network(IPv6.Zero, 0);

    } // struct IPv6Network
} // namespace System.Net.IP

////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    This file was ported from the Coriolis codebase to Singularity.
//

namespace System.Net
{

    using System;
    using System.Net.Sockets;
    using System.Text;
    using System.Globalization;

    // a little perf app measured these times when comparing the internal
    // buffer implemented as a managed byte[] or unmanaged memory IntPtr
    // that's why we use byte[]
    // byte[] total ms:19656
    // IntPtr total ms:25671

    public class SocketAddress {

        internal int m_Size;
        internal byte[] m_Buffer;

        private const int WriteableOffset = 2;
        private const int MaxSize = 32; // IrDA requires 32 bytes
        private bool m_changed = true;
        private int m_hash;

        public AddressFamily Family {
            get {
                int family;
#if BIGENDIAN
                family = ((int)m_Buffer[0]<<8) | m_Buffer[1];
#else
                family = m_Buffer[0] | ((int)m_Buffer[1]<<8);
#endif
                return (AddressFamily)family;
            }
        }
        //
        // Size of this SocketAddress
        //
        public int Size {
            get {
                return m_Size;
            }
        }

        //
        // access to unmanaged serialized data. this doesn't
        // allow access to the first 2 bytes of unmanaged memory
        // that are supposed to contain the address family which
        // is readonly.
        //
        public byte this[int offset] {
            get {
                //
                // access
                //
                if (offset < 0 || offset >= Size) {
                    throw new IndexOutOfRangeException();
                }
                return m_Buffer[offset];
            }
            set {
                if (offset < 0 || offset >= Size) {
                    throw new IndexOutOfRangeException();
                }
                if (m_Buffer[offset] != value) {
                    m_changed = true;
                }
                m_Buffer[offset] = value;
            }
        }

        public SocketAddress(AddressFamily family) : this(family, MaxSize) {
        }

        public SocketAddress(AddressFamily family, int size) {
            if (size < WriteableOffset) {
                //
                // it doesn't make sense to create a socket address with less than
                // 2 bytes, that's where we store the address family.
                //
                throw new ArgumentOutOfRangeException("size");
            }
            m_Size = size;
            byte[] buf = m_Buffer = new byte[(size/IntPtr.Size+2)*IntPtr.Size];//sizeof DWORD

#if BIGENDIAN
            buf[0] = unchecked((byte)((int)family>>8));
            buf[1] = unchecked((byte)((int)family   ));
#else
            buf[0] = unchecked((byte)((int)family   ));
            buf[1] = unchecked((byte)((int)family>>8));
#endif
        }

        //
        // Can be called after the above method did work
        //
        internal int GetAddressSizeOffset()
        {
            return m_Buffer.Length-IntPtr.Size;
        }

        public override bool Equals(object comparand) {
            SocketAddress castedComparand = comparand as SocketAddress;
            if (castedComparand == null || this.Size != castedComparand.Size) {
                return false;
            }
            for (int i = 0; i < this.Size; i++) {
                if (this[i] != castedComparand[i]) {
                    return false;
                }
            }
            return true;
        }

        public override int GetHashCode() {
            if (m_changed) {
                m_changed = false;
                m_hash = 0;

                int i;
                int size = Size & ~3;

                for (i = 0; i < size; i += 4) {
                    m_hash ^= (int)m_Buffer[i]
                            | ((int)m_Buffer[i+1] << 8)
                            | ((int)m_Buffer[i+2] << 16)
                            | ((int)m_Buffer[i+3] << 24);
                }
                if ((Size & 3) != 0) {

                    int remnant = 0;
                    int shift = 0;

                    for (; i < Size; ++i) {
                        remnant |= ((int)m_Buffer[i]) << shift;
                        shift += 8;
                    }
                    m_hash ^= remnant;
                }
            }
            return m_hash;
        }

        public override string ToString() {
            StringBuilder bytes = new StringBuilder();
            for (int i = WriteableOffset; i < this.Size; i++) {
                if (i > WriteableOffset) {
                    bytes.Append(",");
                }
                bytes.Append(this[i].ToString());
            }
            return Family.ToString() + ":" + Size.ToString() + ":{" + bytes.ToString() + "}";
        }

    } // class SocketAddress


} // namespace System.Net

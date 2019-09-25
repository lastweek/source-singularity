// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

using System.Collections;
using System.Diagnostics;
using System.Text;
using System;

using Drivers.Net;

namespace NetStack.Common
{
    // A simple implementation of IBuffer over a single array
    public class SimpleBuffer : IBuffer
    {
        // State
        protected byte [] data;
        protected int position;
        protected int count;

        // IBuffer methods
        public int Available
        {
            get { return count - position; }
        }

        public int Length
        {
            get { return count; }
        }

        public bool Read8(out byte x)
        {
            if (position + 1 > count) {
                x = 0;
                return false;
            }
            x = data[position++];
            return true;
        }

        public bool ReadNet16(out ushort x)
        {
            if (position + 2 > count) {
                x = 0;
                return false;
            }
            x = NetworkBitConverter.ToUInt16(data, position);
            position += 2;
            return true;
        }

        public bool ReadNet32(out uint x)
        {
            if (position + 4 > count) {
                x = 0;
                return false;
            }
            x = NetworkBitConverter.ToUInt32(data, position);
            position += 4;
            return true;
        }

        public bool ReadNet64(out ulong x)
        {
            if (position + 8 > count) {
                x = 0;
                return false;
            }
            x = NetworkBitConverter.ToUInt64(data, position);
            position += 8;
            return true;
        }

        public bool ReadBytes(byte [] buf, int at, int n)
        {
            if (position + n > count)
                return false;

            for (int i = 0; i < n; i++)
                buf[at+i] = data[position++];
            return true;
        }

        public bool ReadEthernetAddress(out EthernetAddress address)
        {
            try {
                address = EthernetAddress.ParseBytes(data, position);
                position += EthernetAddress.Length;
            }
            catch (ArgumentException) {
                address = EthernetAddress.Zero;
                return false;
            }
            return true;
        }

        public bool ReadZeroTerminatedString(out string s)
        {
            int  start = position;
            byte b;

            while (Read8(out b) != false) {
                if (b == 0) {
                    int  length = position - start;
                    ASCIIEncoding ascii = new ASCIIEncoding();
                    s = ascii.GetString(data, start, length);
                    return true;
                }
            }

            s = null;
            position = start;
            return false;
        }

        public byte PeekAvailable(int offset)
        {
            int x = position + offset;
            if (x > count)
                throw new IndexOutOfRangeException();
            return this.data[x];
        }

        public int Position
        {
            get
            {
                return position;
            }
        }

        public SimpleBuffer(int length)
        {
            this.count    = length;
            this.position = 0;
            this.data     = new byte[length];
        }

        public SimpleBuffer(byte [] buffer)
            : this(buffer, 0, buffer.Length)
        {
        }

        // count is the number of bytes in the buffer (not necessarily equal
        // to buf.Length), count=the number of bytes from index (include) to the end
        public SimpleBuffer(byte [] buffer, int start, int length)
        {
            this.position = start;
            this.count    = start + length;
            this.data     = buffer;

            //this.position = 0;
            //this.count    = length;
            //this.data     = new byte[length];
            //Array.Copy(buffer, start, this.data, 0, this.count);
        }
    } // SimpleBuffer
} // namespace Drivers.Net

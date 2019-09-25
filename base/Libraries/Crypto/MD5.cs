////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    A simple MD5 hash implementation. Ported from C++ code,
//    originally used in the Rotor / Coriolis codebase.
//
//      For algorithmic background see (for example)
//
//           Bruce Schneier
//           Applied Cryptography
//           Protocols, Algorithms, and Source Code in C
//           Second Edition
//           Wiley, 1996
//           ISBN 0-471-12845-7
//           QA76.9 A25S35
//
//           Alfred J. Menezes et al
//           Handbook of Applied Cryptography
//          The CRC Press Series on Discrete Mathematics
//                  and its Applications
//           CRC Press LLC, 1997
//           ISBN 0-8495-8523-7
//           QA76.9A25M643
//
//       Also see RFC (Request For Comments) 1321 from April, 1992.
//

using System;
using System.Diagnostics;

namespace Microsoft.Singularity.Crypto
{
    public class MD5
    {
        // Data awaiting full 512-bit block.
        // Length (nbit_total[0] % 512) bits.
        // Unused part of buffer (at end) is zero.
        private uint[] Waiting_Data; // uint[16]

        // Hash through last full block
        private uint[] Partial_Hash; // uint[4]

        // Total length of message so far
        // (bits, mod 2^64)
        private uint[] NBit_Total; // uint[2]

        private static readonly uint[] MD5_Const = new uint[] {
            // Round 1
            0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
            0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
            0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
            0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,

            // Round 2
            0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
            0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
            0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
            0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,

            // Round 3
            0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
            0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
            0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
            0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,

            // Round 4
            0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
            0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
            0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
            0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
        };

        public MD5()
        {
            Waiting_Data = new uint[16];
            NBit_Total = new uint[2];
            Partial_Hash = new uint[4];
        }

        public byte[] Hash(byte[] data)
        {
            Reset();
            Update(data);
            return Finish();
        }

        private void Reset()
        {
            for (uint i = 0; i != 16; i++) {
                Waiting_Data[i] = 0;
            }

            NBit_Total[0] = NBit_Total[1] = 0;

            //
            // Initialize hash variables.
//
            // N.B.  The initial values in RFC 1321 appear
            // in byte-reversed order.  Bruce Schneier's
            // 2nd edition neglects to rearrange them.
            //
            Partial_Hash[0] = 0x67452301;
            Partial_Hash[1] = 0xefcdab89;
            Partial_Hash[2] = ~Partial_Hash[0];
            Partial_Hash[3] = ~Partial_Hash[1];
        }

        // Shift val left by num bits, wrapping bits around.
        private uint RotL(uint val, byte num)
        {
            Debug.Assert(num < 32);
            uint overflowBits = val >> (32 - num);
            val = val << num;
            val |= overflowBits;
            return val;
        }

        //
        //Update the MD5 hash from a fresh 64 bytes of data.
        //
        private void ProcessBlock()
        {
            uint a = Partial_Hash[0], b = Partial_Hash[1];
            uint c = Partial_Hash[2], d = Partial_Hash[3];
            uint[] msg16 = new uint[32];   // Two copies of message
            int i;
            int consindex = 0;

            for (i = 0; i != 16; i++) {
                // Copy to local array, zero original
                // Make two copies, to simplify indexing
                uint datval = Waiting_Data[i];
                Waiting_Data[i] = 0;
                msg16[i] = msg16[i+16] = datval;
            }

            // Round 1
            for (i = -16; i != 0; i += 4) {
                // Rewrite (X & Y) | (~X & Z)  as  Z ^ (X & (Y ^ Z))
                // [Easily validated by checking X = 0 and X = 1 cases.]
                // This avoids ANDNOT (which X86 lacks) and needs only
                // one temporary register.
                // On register-rich architectures, the Y ^ Z computation
                // can start early, before X is computed.
                a += msg16[i+16] + MD5_Const[consindex] + (d ^ (b & (c ^ d)));
                a = b + RotL(a, 7);
                consindex++;

                d += msg16[i+17] + MD5_Const[consindex] + (c ^ (a & (b ^ c)));
                d = a + RotL(d, 12);
                consindex++;

                c += msg16[i+18] + MD5_Const[consindex] + (b ^ (d & (a ^ b)));
                c = d + RotL(c, 17);
                consindex++;

                b += msg16[i+19] + MD5_Const[consindex] + (a ^ (c & (d ^ a)));
                b = c + RotL(b, 22);
                consindex++;
            }

            // Round 2
            for (i = -16; i != 0; i += 4) {
                // Rewrite (Z & X) | (~Z & Y)  as  Y ^ (Z & (X ^ Y))
                a += msg16[i+17] + MD5_Const[consindex] + (c ^ (d & (b ^ c)));
                a = b + RotL(a, 5);
                consindex++;

                d += msg16[i+22] + MD5_Const[consindex] + (b ^ (c & (a ^ b)));
                d = a + RotL(d, 9);
                consindex++;

                c += msg16[i+27] + MD5_Const[consindex] + (a ^ (b & (d ^ a)));
                c = d + RotL(c, 14);
                consindex++;

                b += msg16[i+16] + MD5_Const[consindex] + (d ^ (a & (c ^ d)));
                b = c + RotL(b, 20);
                consindex++;
            }

            // Round 3
            for (i = 16; i != 0; i -= 4) {
                a += msg16[i+5]  + MD5_Const[consindex] + ((b ^ c) ^ d);
                a = b + RotL(a, 4);
                consindex++;

                d += msg16[i+8]  + MD5_Const[consindex] + (a ^ (b ^ c));
                d = a + RotL(d, 11);
                consindex++;

                c += msg16[i+11] + MD5_Const[consindex] + ((d ^ a) ^ b);
                c = d + RotL(c, 16);
                consindex++;

                b += msg16[i+14] + MD5_Const[consindex] + (c ^ (d ^ a));
                b = c + RotL(b, 23);
                consindex++;
            }

            // Round 4
            for (i = 16; i != 0; i -= 4) {
                a += msg16[i  ]  + MD5_Const[consindex] + (c ^ (~d | b));
                a = b + RotL(a, 6);
                consindex++;

                d += msg16[i+7]  + MD5_Const[consindex] + (b ^ (~c | a));
                d = a + RotL(d, 10);
                consindex++;

                c += msg16[i+14] + MD5_Const[consindex] + (a ^ (~b | d));
                c = d + RotL(c, 15);
                consindex++;

                b += msg16[i+5]  + MD5_Const[consindex] + (d ^ (~a | c));
                b = c + RotL(b, 21);
                consindex++;
            }

            Debug.Assert(consindex == 64);

            Partial_Hash[0] = unchecked(Partial_Hash[0] + a);
            Partial_Hash[1] = unchecked(Partial_Hash[1] + b);
            Partial_Hash[2] = unchecked(Partial_Hash[2] + c);
            Partial_Hash[3] = unchecked(Partial_Hash[3] + d);
        }

        //
        //Append data to a partially hashed MD5 message.
        //
        private void Update(byte[] data)
        {
            uint nbit_occupied = NBit_Total[0] & 511;
            uint nbitnew_low = unchecked((uint)(8 * data.Length));
            uint dataIndex = 0, waitingDataIndex;

            Debug.Assert((nbit_occupied & 7) == 0);   // Partial bytes not implemented
            NBit_Total[0] += nbitnew_low;
            NBit_Total[1] += (uint)(data.Length >> 29);

            if (NBit_Total[0] < nbitnew_low) {
                // Overflow (?)
                NBit_Total[1]++;
            }

            // Advance to word boundary in waiting_data   
            if ((nbit_occupied & 31) != 0) {
                waitingDataIndex = nbit_occupied / 32;

                while ((nbit_occupied & 31) != 0 && dataIndex < data.Length) {
                    Waiting_Data[waitingDataIndex] |= (uint)data[dataIndex] << (int)(nbit_occupied & 31);
                    dataIndex++;
                    nbit_occupied += 8;
                }
            } // if nbit_occupied

            // Transfer 4 bytes at a time   
            do
            {
                uint nword_occupied = nbit_occupied/32;
                uint nwcopy = Math.Min((uint)((data.Length - dataIndex)/4), (uint)(16 - nword_occupied));
                Debug.Assert(nbit_occupied <= 512);
                Debug.Assert((nbit_occupied & 31) == 0 || (dataIndex == data.Length));
                waitingDataIndex = nword_occupied;
                nbit_occupied += 32*nwcopy;

                while (nwcopy != 0) {
                    uint byte0 = (uint)data[dataIndex++];
                    uint byte1 = (uint)data[dataIndex++];
                    uint byte2 = (uint)data[dataIndex++];
                    uint byte3 = (uint)data[dataIndex++];
                    Waiting_Data[waitingDataIndex++] = // Little endian   
                        byte0 | (byte1 << 8) | (byte2 << 16) | (byte3 << 24);
                    nwcopy--;
                }

                if (nbit_occupied == 512) {
                    ProcessBlock();
                    nbit_occupied = 0;
                    waitingDataIndex -= 16;
                    Debug.Assert(waitingDataIndex == 0);
                }
            } while (dataIndex <= (data.Length - 4));

            Debug.Assert(waitingDataIndex == nbit_occupied/32);

            while (dataIndex < data.Length) {
                uint new_byte = (uint)data[dataIndex++];
                Debug.Assert((nbit_occupied & 31) <= 16);
                Waiting_Data[waitingDataIndex] |= new_byte << (int)(nbit_occupied & 31);
                nbit_occupied += 8;
            }

            Debug.Assert(nbit_occupied == (NBit_Total[0] & 511));
        }

        //
        //Finish an MD5 hash.
        //
        private byte[] Finish()
        {
            uint nbit0 = NBit_Total[0];
            uint nbit1 = NBit_Total[1];
            uint nbit_occupied = nbit0 & 511;
            uint i;

            Debug.Assert((nbit_occupied & 7) == 0);

            // Append a 1 bit
            Waiting_Data[nbit_occupied/32] |=
                (uint)0x80 << (int)(nbit_occupied & 31);

            nbit_occupied += 8;

            // TBD -- Above seems weird -- why number bytes from the
            //        least significant end but number bits the other way?

            // Append zero bits until length (in bits) is 448 mod 512.
            // Then append the length, in bits.
            // Here we assume the buffer was zeroed earlier.
            if (nbit_occupied > 448) // If fewer than 64 bits left
            {
                ProcessBlock();
                nbit_occupied = 0;
            }

            Waiting_Data[14] = nbit0;
            Waiting_Data[15] = nbit1;
            ProcessBlock();

            // Copy final digest to byte array   

            byte[] digest = new byte[16];

            for (i = 0; i != 4; i++) {
                uint dwi = Partial_Hash[i];

                // Little-endian
                digest[4*i    ] = (byte)(dwi         & 255);
                digest[4*i + 1] = (byte)((dwi >>  8) & 255);
                digest[4*i + 2] = (byte)((dwi >> 16) & 255);
                digest[4*i + 3] = (byte)((dwi >> 24) & 255);
            }

            return digest;
        }
    }
}

// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Text;
using System.Collections;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Drivers;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.V1.Services;


namespace Iso9660 
{
    
    /// <summary>
    /// This class contains a number of static methods for marshalling,
    /// unmarshalling, and comparing byte arrays.
    /// </summary>
    public class ByteArray {
        private const int MIN = -1;
        private const int MAX = -2;
            

        /// <summary>
        /// Marshalls a byte array into a buffer starting at a pointer 
        /// into the buffer, and advances the pointer accordingly.
        /// </summary>
        /// <param name="b">The byte array that is being marshalled.</param>
        /// <param name="bytes">The buffer into which the integer is 
        /// marshalled.
        /// </param>
        /// <param name="offset">The position in the buffer where the Handle 
        /// starts.After completion, offset is the next position after the 
        /// Handle.</param>
        public static void Marshall(byte[] b, byte[] bytes, ref int offset) {
            if (b == Minimum) {
                Int.Marshall(MIN, bytes, ref offset);
            }
            else if (b == Maximum) {
                Int.Marshall(MAX, bytes, ref offset);
            }
            else {
                if (b != null) {
                    Int.Marshall(b.Length, bytes, ref offset);
                    Array.Copy(b, 0, bytes, offset, b.Length);
                    offset += b.Length;
                }
                else {
                    Int.Marshall(0, bytes, ref offset);
                }
            }
        }

        public static int Sizeof(byte[] b) {
            if (b == Minimum || b == Maximum) {
                return Int.Size;
            }
            if (b == null) {
                return Int.Size;
            }
            return Int.Size + b.Length;
        }

        /// <summary>
        /// Given a buffer and a pointer into it, unmarshalls a byte array 
        /// from the buffer, advancing the pointer by 4 bytes.
        /// </summary>
        /// <param name="bytes">The buffer from which the byte array is 
        /// unmarshalled.</param>
        /// <param name="offset">The position in the buffer where the Handle 
        /// starts.
        /// After completion, offset is the next position after the Handle.
        /// </param>
        /// <returns>The byte array that was unmarshalled.</returns>
        ///
        /// Note that our marshall and unmarshall routines are not symmetric
        /// I.e., We marshall a null string as a string of zero length. But
        /// unmarshalling a 0 length string does not result in  a null string
        /// but in a string with zero length.
        /// I believe the B-Tree recovery procedures cannot deal with an
        /// unmarshalled string that is a null.

        public static byte[] Unmarshall(byte[] bytes, ref int offset) {
            int len = Int.Unmarshall(bytes, ref offset);
            if (len == MIN) {
                return Minimum;
            }
            else if (len == MAX) {
                return Maximum;
            }
            else {
                if (len < 0) {
                    DebugStub.WriteLine("ba len is negative " + len);
                    system.panic("bad len");
                }
                if (len == 0) {
                    //Console.WriteLine("BA LEN is 0 ");
                }
                byte[] b = new byte[len];
                try {
                    Array.Copy(bytes, offset, b, 0, b.Length);
                    offset += b.Length;
                    return b;
                } 
                catch (Exception) {
                    DebugStub.WriteLine("len = " + len + 
                                      " b.Length " + b.Length +
                                      " offset: " + offset + 
                                      " bytes.Length " + bytes.Length); 
                    throw;
                }
            }
        }

        /// <summary>
        /// Given a buffer and a pointer into it, unmarshalls the length of a 
        /// byte array  from the buffer, but does not advance the pointer.
        /// </summary>
        /// <param name="bytes">The buffer from which the byte array 
        /// is unmarshalled.</param>
        /// <param name="offset">The position in the buffer where the Handle 
        /// starts. After completion, offset is the next position after 
        /// the Handle.</param>
        /// <returns>The byte array that was unmarshalled.</returns>

        public static int UnmarshallLength(byte[] bytes, int offset) {
            int len = Int.Unmarshall(bytes, ref offset);
            return len < 0 ? 0 : len;
        }

        /// <summary>
        /// This constant identifies the minimum byte array, i.e. the byte 
        /// array that, when compared (via Comparer.Compare) with any other 
        /// byte array, is smaller.
        /// </summary>
        public static readonly byte[] Minimum = new byte[0];

        /// <summary>
        /// This constant identifies the maximum byte array, i.e. the byte 
        /// array that, when compared (via Comparer.Compare) with any other 
        /// byte array, is larger.
        /// </summary>
        public static readonly byte[] Maximum = new byte[0];

        public delegate int CompareTo(byte[] a, byte[] b);

        static public int LexicographicCompareTo(byte[] a, byte[] b) {
            int min = System.Math.Min(a.Length, b.Length);
            int i = 0;
            for (; i < min; i++) {
                if (a[i] < b[i]) return -1;
                if (a[i] > b[i]) return + 1;
            }
            if (a.Length < b.Length) return -1;
            if (a.Length > b.Length) return + 1;
            return 0;
        }

        /// <summary>
        /// Returns the string representation of a byte array. Returns 
        /// "null" if the byte array is null, and "Maximum" if the byte
        /// array is identical to Maximum.
        /// </summary>
        /// <param name="b"></param>
        /// <returns></returns>
        public static string ToString(byte[] b) {
            if (b == Minimum) return "Minimum";
            if (b == Maximum) return "Maximum";
            if (b == null) return "null";
            char[] c = new char[b.Length];
            for (int i = 0; i < c.Length; i++) c[i] = (char)b[i];
            return new string(c);
        }

        /// <summary>
        /// for debugging -- return a hex version of the array that can 
        /// be printed on the console
        /// </summary>
        /// <param name="s"></param>
        /// <returns></returns>
        
        public static string ToLegibleString(byte[] b) {
            return ToLegibleString(new ByteContainer(b));
        }

        public static string ToLegibleString(ByteContainer b) {
            byte[] temp = b.ConvertToArray();
            StringBuilder legible = new StringBuilder();
            for (int i = 0; i < temp.Length; i++) {
                legible.AppendFormat("{0:x2}", temp[i]);
            }
            return legible.ToString();
        }

        public static string ToLegibleString(byte[] b, int off, int len) {
            return ToLegibleString(new ByteContainer(b), off, len);
        }

        public static string ToLegibleString(ByteContainer b, int off, int len) {
            byte[] temp = b.ConvertToArray();
            system.Assert(len + off <= temp.Length);
            StringBuilder legible = new StringBuilder();
            for (int i = off; i < off + len; i++) {
                legible.AppendFormat("{0:x2}", temp[i]);
            }
            return legible.ToString();
        }

        public static string ToLegibleString(byte[] b, int len) {
            return ToLegibleString(new ByteContainer(b), len);
        }

        public static string ToLegibleString(ByteContainer b, int len) {
            byte[] temp = b.ConvertToArray();
            system.Assert(len < temp.Length);
            StringBuilder legible = new StringBuilder();
            for (int i = 0; i < len; i++) {
                legible.AppendFormat("{0:x2}", temp[i]);
            }
            return legible.ToString();
        }

        public static byte[] ToByteArray(string s) {
            byte[] b = new byte[s.Length];
            for (int i = 0; i < s.Length; i++) {
                b[i] = (byte)(s[i] & 0xff);
            }
            return b;
        }


        /// <summary>
        /// general purpose string-byte array transformation
        /// </summary>
        /// <param name="s"></param>
        /// <returns></returns>
        public static byte[] StringToByteArray(string s) {
            if (s == null) {
                return null;
            }
            byte[] b = new byte[s.Length];
            for (int i = 0; i < s.Length; i++) {
                b[i] = (byte)(s[i] & 0xff);
            }
            return b;
        }

        public static string ToString(byte[] b, int count) {
            if (b == null) {
                return "null";
            }
            int len;
            if (count < b.Length) {
                len = count;
            }
            else {
                len = b.Length;
            }
            char[] c = new char[len];
            for (int i = 0; i < len; i++) {
                c[i] = (char)b[i];
            }
            return new string(c);
        }

        public static string ToString(byte[] b, int off, int len) {

            char[] c = new char[len];
            for (int i = 0; i < len; i++) {
                c[i] = (char)b[off+i];
            }
            return new string(c);
        }

        public static ulong ToUlong(byte[] b, int off) { // little-endian

            ulong x = 0;
            for (int i = 0; i < 4; i++) {
                x <<= 8; x += b[off+i];
            }
            return x;
        }

        public static ushort ToUshort(byte[] b, int off) { // little-endian

            ushort x = 0;
            for (int i = 0; i < 2; i++) {
                x <<= 8; x += b[off+i];
            }
            return x;
        }

        public static int  SizeofString(string s) {
            return Int.Size + s.Length;
        }

        public static void MarshallString(string s, byte[] bytes, ref int off){
            
            Int.Marshall(s.Length, bytes, ref off);
            for (int i = 0; i < s.Length; i++) {
                bytes[off++] = (byte)(s[i] & 0xff);
            }
        }

        public static string UnmarshallString(byte[] bytes, ref int offset){
            int len = Int.Unmarshall(bytes, ref offset);
            if (len <= 0) {
                Tracing.Log(Tracing.Debug,"bytes had a negative len="+len);
                return null; 
            }
            char[] c = new char[len];
            for (int i = 0; i < len; i++) {
                c[i] = (char)bytes[offset++];
            }
            return new string(c);
        }



        public class Comparer {
            public readonly CompareTo RawCompareTo;

            public Comparer() {
                this.RawCompareTo = new CompareTo(LexicographicCompareTo);
            }

            public Comparer(CompareTo rawComp) {
                this.RawCompareTo = rawComp;
            }

            public int Compare(byte[] a, byte[] b) {
                if ((a == Minimum && b == Minimum) || 
                    (a == Maximum && b == Maximum)) {
                    return 0;
                }
                else if (a == Minimum || b == Maximum) {
                    return -1;
                }
                else if (b == Minimum || a == Maximum) {
                    return +1;
                }
                else {
                    return this.RawCompareTo(a, b);
                }
            }
        }
    }
}

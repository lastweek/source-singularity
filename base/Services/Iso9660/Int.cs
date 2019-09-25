// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace Iso9660
{
	/// <summary>
	/// This class contains static methods for marshalling and unmarshalling
	/// 32-bit integers.
	/// </summary>
    public class Int {
        /// <summary>
        /// The size (in bytes) of the marshalled representation of an integer.
        /// </summary>
        public const int Size = 4;

        /// <summary>
        /// Marshalls an integer into a buffer starting at a pointer into the 
        /// buffer, and advances the pointer accordingly. 
        /// </summary>
        /// <param name="i">The integer that is being marshalled.</param>
        /// <param name="bytes">The buffer into which the integer is marshalled.</param>
        /// <param name="offset">The position in the buffer where the Handle starts.
        /// After completion, offset is the next position after the Handle.</param>
        public static void Marshall(int i, byte[] bytes, ref int offset) {
            bytes[offset+0] = (byte)(i & 0xff); i >>= 8;
            bytes[offset+1] = (byte)(i & 0xff); i >>= 8;
            bytes[offset+2] = (byte)(i & 0xff); i >>= 8;
            bytes[offset+3] = (byte)(i & 0xff); i >>= 8;
            offset += 4;
        }

        /// <summary>
        /// Given a buffer and a pointer into it, unmarshalls an integer from the 
        /// buffer, advancing the pointer by 4 bytes.
        /// </summary>
        /// <param name="bytes">The buffer from which the integer is unmarshalled.</param>
        /// <param name="offset">The position in the buffer where the Handle starts.
        /// After completion, offset is the next position after the Handle.</param>
        /// <returns>The integer that was unmarshalled.</returns>
        public static int Unmarshall(byte[] bytes, ref int offset) {
            int i = 0;
            i = (i << 8) | bytes[offset+3];
            i = (i << 8) | bytes[offset+2];
            i = (i << 8) | bytes[offset+1];
            i = (i << 8) | bytes[offset+0];
            offset += 4;
            return i;
        }
        
        public static int Parse(string val) {
            int num;
            if (val.Length > 2 && val[0] == '0' && 
                             (val[1] == 'x' || val[1] == 'X')) {
                num = System.Int32.Parse(val.Substring(2), 
                          System.Globalization.NumberStyles.AllowHexSpecifier);
            }
            else {
                num = System.Int32.Parse(val);
            }
            return num;
        }
    }
}

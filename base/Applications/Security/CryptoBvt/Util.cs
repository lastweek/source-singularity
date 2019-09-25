///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Text;

class Util
{
    public const string HexDigits = "0123456789abcdef";

    public static string! ByteArrayToStringHex(byte[]! buffer, int index, int length)
    {
        StringBuilder sb = new StringBuilder(length * 2);
        for (int i = 0; i < length; i++) {
            byte b = buffer[index + i];
            sb.Append(HexDigits[b >> 4]);
            sb.Append(HexDigits[b & 0xf]);
        }
        return sb.ToString();
    }

    public static string! ByteArrayToStringHex(byte[]! buffer)
    {
        return ByteArrayToStringHex(buffer, 0, buffer.Length);
    }

    static byte CharToHex(char c)
    {
        if (c >= '0' && c <= '9')
            return (byte)(c - '0');
        if (c >= 'a' && c <= 'f')
            return (byte)(c - 'a' + 10);
        if (c >= 'A' && c <= 'F')
            return (byte)(c - 'A' + 10);
        throw new ArgumentException("Invalid hex char");
    }

    public static byte[]! HexStringToByteArray(string! str)
    {
        if ((str.Length % 2) != 0)
            throw new Exception("Input string cannot be odd in length.");

        byte[] result = new byte[str.Length / 2];
        for (int i = 0; i < result.Length; i++) {
            byte high = CharToHex(str[i * 2]);
            byte low = CharToHex(str[i * 2 + 1]);
            result[i] = (byte)((high << 4) | low);
        }

        return result;
    }

    public static int CompareArraySpans(byte[]! array1, int offset1, byte[]! array2, int offset2, int length)
    {
        for (int i = 0; i < length; i++) {
            byte element1 = array1[i];
            byte element2 = array2[i];
            if (element1 < element2)
                return -1;
            if (element1 > element2)
                return 1;
        }

        return 0;
    }


        public static void DumpBuffer(byte[]! buffer)
        {
            DumpBuffer(buffer, 0, buffer.Length);
        }

        public static void DumpBuffer(byte[]! buffer, int index, int length)
        {
            StringBuilder line = new StringBuilder();

            for (int i = 0; i < length; i += 0x10) {
                line.Length = 0;
                line.AppendFormat("{0:x04}: ", i);

                for (int j = 0; j < 0x10; j++) {

                    if (i + j < length) {
                        line.Append(" ");
                        byte b = buffer[index + i + j];
                        line.Append((Char)HexDigits[b >> 4]);
                        line.Append((Char)HexDigits[b & 0xf]);
                    }
                    else {
                        line.Append("   ");
                    }
                }

                line.Append(" : ");
                for (int j = 0; j < 0x10; j++) {

                    if (i + j < length) {
                        byte b = buffer[index + i + j];
                        if (b >= 32 && b <= 127) {
                            line.Append((Char)b);
                        }
                        else {
                            line.Append(".");
                        }
                    }
                    else {
                        break;
                    }
                }

                Console.WriteLine(line.ToString());
            }
        }

}

///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Collections.Generic;
using System.Text;

namespace CryptoBvt
{
    class Program
    {
        static void Main(string[] args)
        {
            MD4Test.VerifyKnownDigests();
            DesTest.RunTests();
        }
    }

    class Util
    {
        public const string HexDigits = "0123456789abcdef";

        public static string! ByteArrayToString(byte[]! buffer, int index, int length)
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
            return ByteArrayToString(buffer, 0, buffer.Length);
        }
    }
}

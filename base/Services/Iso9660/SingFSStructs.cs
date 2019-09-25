// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using Microsoft.Contracts;

namespace Iso9660
{
    public struct Iso9660Ptr {
        public byte[] buf;
        public int pos;

        public Iso9660Ptr(byte[] newbuf, int newpos) {
            buf = newbuf;
            pos = newpos;
        }

        public void Reset() {
            buf = new byte[buf.Length];
            pos = 0;
        }
    }

    [Flags]
    public enum Iso9660FileFlags : uint {
        Normal=0,
        Directory=2,
    }

    public struct Iso9660FileAttributes {
        public Iso9660FileFlags flags;
        public long size;
    }

    public class Iso9660IOException : IOException {
        public Iso9660IOException(string str) : base(str) {}
    }

    public class DirEnt {

        public const int LEN      =  0; // 1 byte
        public const int BLOCK_NO =  6; // 4-byte LE int
        public const int SIZE     = 14; // 4-byte LE int
        public const int FLAGS    = 25; // 1 byte
        public const int NAME_LEN = 32; // 1 byte
        public const int NAME     = 33; // <NAME_LEN> chars
    }

    public class SuperBlock {

        public const int TYPE     =   0; // 1 byte (SB => 0x01)
        public const int IDENT    =   1; // 5 chars ("CD001")

        public const int LABEL    =  40; // 32 chars
        public const int SET_SIZE = 122; // 2-byte LE int
        public const int SEQ_NO   = 126; // 2-byte LE int
        public const int BLK_SIZE = 130; // 2-byte LE int

        public const int ROOT_DIR = 156; // Root's DirEnt

        public const string DELIMITER = "/";

        internal static Iso9660DirectoryInfo root;

        public static Iso9660DirectoryInfo Root {
            get{return root;}
        }

        static SuperBlock() {}
    }
}

// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;

namespace Iso9660
{
	public class Iso9660FileInfo : Iso9660FileSystemInfo
	{
        internal Iso9660FileInfo() {}

        public Iso9660FileStream Open(FileMode mode, FileAccess access) {
            return new Iso9660FileStream(this, mode, access);
        }

        public Iso9660FileStream OpenRead() {
            return Open(System.IO.FileMode.Open,
                        System.IO.FileAccess.Read);
        }

        internal static long BlockSize(long block) {
            return 2048;
        }

        internal long BlockFromByte(long pos) {
            return (long)blockno + pos / 2048;
        }
	}
}

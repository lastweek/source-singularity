// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Text;
using System.Threading;
using Microsoft.Singularity.Security;
using Microsoft.Singularity.V1.Services;

namespace Iso9660
{
    internal class FSObjectGlobalState {
        internal Iso9660FileAttributes attributes;
    }

    public abstract class Iso9660FileSystemInfo
    {
        public ulong blockno;
        
        // embedded FSObjectGlobalState globalState;
        //                  globalState.attributes:

        public ulong size;
        public byte flags;

        // embedded Iso9660Ptr:
        
        public byte[] buf;
        public int pos;

        public Iso9660FileSystemInfo() { buf = new byte[2048];
                                         pos = 0;
        }
        internal void InitializeMe (byte[] buf, int pos) {

            blockno = ByteArray.ToUlong (buf,pos + DirEnt.BLOCK_NO);
            size    = ByteArray.ToUlong (buf,pos + DirEnt.SIZE);
            flags   =                    buf[pos + DirEnt.FLAGS];
        }

        internal static string[] ParsePath(string path) {
            if (path == null) {
                return null;
            }

            return path.Split(new char[] {SuperBlock.DELIMITER[0]});
        }

        // given a path, gives you back a filesystem object representing
        // that path

        public static Iso9660FileSystemInfo InstantiatePath(string path) {
            return InstantiatePath(path, null);
        }

        public static Iso9660FileSystemInfo InstantiatePath(
            string path, Iso9660DirectoryInfo startDir) {

            Iso9660FileSystemInfo child;
            Iso9660DirectoryInfo iterator = (startDir == null) ? SuperBlock.root : startDir;

            if (path == "/" || path == "") {
                return iterator;
            }

            string[] names = ParsePath(path);

            if (names == null) {
                return null;
            }

            int start = (names[0].Length == 0) ? 1 : 0;
            for (int i = start; i < names.Length - 1; i++) {
                if (!iterator.FindChild(names[i], true, out child)) {
                    //throw new ArgumentException("Invalid path");
                    return null;
                }
                else {
                    iterator = (Iso9660DirectoryInfo)child;
                }
            }

            if (!iterator.FindChild(names[names.Length - 1], true, out child)) {
                //throw new ArgumentException("Invalid path");
                return null;
            }
            else {
                return child;
            }
        }
    }
}

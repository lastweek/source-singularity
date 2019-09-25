// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Drivers;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.V1.Services;


namespace Iso9660
{
	public class Iso9660DirectoryInfo : Iso9660FileSystemInfo
	{
        private byte   LEN      { get { return buf[pos + DirEnt.LEN];      }}
        private byte   FLAGS    { get { return buf[pos + DirEnt.FLAGS];    }}

        private int    NAME_LEN { get { return buf[pos + DirEnt.NAME_LEN]; }}
        private int    NAME_POS { get { return     pos + DirEnt.NAME;      }}

        private string NAME     { get { return ByteArray.ToString (buf, NAME_POS, NAME_LEN); }}

        private bool   DOT      { get { return ((NAME_LEN == 1) && (buf[NAME_POS] == 0x00)); }}
        private bool   DOTDOT   { get { return ((NAME_LEN == 1) && (buf[NAME_POS] == 0x01)); }}

        public string myPrefix;

        internal Iso9660DirectoryInfo() {}

        //
        //  0. Delegated "lookup" for Enumerate & FindChild
        //

        private delegate bool LOOKUP (Object obj);

        private bool Lookup (LOOKUP lookup, Object obj) {

            //
            // The following assumes that the list of directory entries
            // is terminated in every block by an entry with LEN 0, ie:
            //
            // 1. directory entries do not cross block boundaries
            //    (with <n> entries in the 1st block, and unused bytes at
            //     the end, entry <n+1> starts at pos 0 in the 2nd block)
            //
            // 2. the size is used only to calculate the number of blocks
            //    (not the last byte of the last entry in the last block)
            //
            
            ulong nblocks = 1 + (size - 1) / 2048;

            for (ulong n = 0; n < nblocks; n++) {

                Iso9660.Stdio.RawDevice.ReadBlock (buf, blockno + n);

                for (pos = 0;; pos += LEN) {

                    if (LEN == 0)
                        break;

                    if (DOT || DOTDOT)
                        continue;
                
                    if (lookup (obj))
                        return true;
                }
            }
            return false;
        }

        //
        //  1. Enumerate (dir/ls)
        //

        private bool Enumerate (Object obj) {

            bool dir = ((FLAGS & (byte)Iso9660FileFlags.Directory) != 0);

            NodeType nodeType = (dir)? NodeType.Directory: NodeType.File;

            ((SortedList)obj).Add (NAME.ToLower(), nodeType); // FIXME: ToLower opt?

            return false; // GetNextChild
        }

        public EnumerationRecords[] in ExHeap Enumerate (out ErrorCode errorOut)
        {
            SortedList matches; 
            EnumerationRecords[] in ExHeap responses = null; 
            
            errorOut = ErrorCode.NoError; 
            matches  = new SortedList();
            if (matches == null) {
                errorOut = ErrorCode.InsufficientResources; 
                return null;
            }
            Lookup (Enumerate, matches);

            responses = new [ExHeap] EnumerationRecords[matches.Count]; 
            if (responses == null) {
                errorOut = ErrorCode.InsufficientResources; 
                return null;
            }
            for (int i = 0; i < matches.Count; i++) {
                expose (responses[i]) {
                    delete responses[i].Path; // checker doesn't know its null.
                    responses[i].Path = Bitter.FromString2((!)((string)matches.GetKey(i))); 
                    responses[i].Type = (NodeType) (!) matches.GetByIndex(i); 
                }
            }
            return responses; 
        }

        //
        //  2. FindChild
        //

        private bool FindChild (Object obj) {
        
            return ((string)obj == NAME.ToLower()); // FIXME: ToLower opt?
        }
        internal bool FindChild(string name, bool returnChild, 
            out Iso9660FileSystemInfo child) {

            if (!Lookup (FindChild, name)) {
                child = null;
                return false;
            }
            if ((FLAGS & (byte)Iso9660FileFlags.Directory) != 0) {

                Iso9660DirectoryInfo dir = new Iso9660DirectoryInfo();
                dir.myPrefix = myPrefix + SuperBlock.DELIMITER + name;
                child = dir;
            }
            else {
                Iso9660FileInfo file = new Iso9660FileInfo();
                child = file;
            }
            child.InitializeMe (buf, pos);
            return true;
        }
	}
}

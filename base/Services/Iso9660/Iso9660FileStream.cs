// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;

using Microsoft.Contracts;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

namespace Iso9660
{
    public class Iso9660FileStream {
        private Iso9660FileInfo _info;
        private long _pos = 0;

        [NotDelayed]
        public Iso9660FileStream(Iso9660FileInfo info, FileMode mode,
            FileAccess access) {
            _info = info;
            _pos = 0;
        }

        ~Iso9660FileStream() {}

        public bool CanRead {
            get {
                return true;
            }
        }

        public bool CanWrite {
            get {
                return false;
            }
        }

        public bool CanSeek {
            get {
                return true;
            }
        }

        public long Length {
            get {
                long size = (long)_info.size;
                return size;
            }
        }

        public long Position {
            get {
                return _pos;
            }
        }

        public void Close() {
        }

        public int Read(ByteContainer buffer, int offset, int count) {
            Tracing.Log(Tracing.Debug,"Entered");

            long currentLength = (long)_info.size;

            // just touch the file
            if (count == 0 || _pos >= currentLength) {
                return 0;
            }

            long bytesLeft;

            if (currentLength - _pos > (long)count) {
                bytesLeft = (long)count;
            }
            else {
                bytesLeft = currentLength - _pos;
            }

            ////
            //Console.WriteLine("ReadArgs: count = " + args.count +
            //                " offset = " + args.offset +
            //                " bytes to be read " + bytesLeft);
            //  

            if (buffer == null) {
                //Console.WriteLine("ReadNFS: user buffer was null!");
                throw new ArgumentNullException("Buffer given to Read was null");
            }
            else if ((long)buffer.Length < bytesLeft) {
                    throw new ArgumentException("Not enough room in buffer");
            }

            long uBufOff = (long)offset; // offset into user's buffer;
            long curFileOff = _pos;
            long blockno = -1;

            while (bytesLeft > 0) {
                long curBlk = _info.BlockFromByte(curFileOff);
                long curBlkSize = Iso9660FileInfo.BlockSize(curBlk);
                long curBlkOff = curFileOff % curBlkSize;

                ////
                //Console.WriteLine("ReadArgs: curBlockNum " + curBlk +
                //                " curBlkSize = " + curBlkSize +
                //                " cur offset into blk " + curBlkOff);
                //  
                if (blockno < curBlk) {
                    blockno = curBlk;

                    //
                    //  1. fetch data from media's block
                    //

                    Iso9660.Stdio.RawDevice.ReadBlock (_info.buf, (ulong)blockno);
                }
                long dist;
                if (curBlkSize - curBlkOff > bytesLeft) {
                    dist = bytesLeft;
                }
                else {
                    dist = curBlkSize - curBlkOff;
                }

                //
                //  2. store data into user's buffer
                //

                buffer.CopyTo (_info.buf, (int)curBlkOff, (int)uBufOff, (int)dist);

                uBufOff += dist;
                curFileOff += dist;
                bytesLeft -= dist;
            }

            _pos += uBufOff;
            return (int)uBufOff;
            Tracing.Log(Tracing.Debug,"Exit");
        }

        public long Seek(long offset, System.IO.SeekOrigin origin) {
            Tracing.Log(Tracing.Debug,"Entered");
            switch (origin) {
                case System.IO.SeekOrigin.Begin:
                    if (offset >= 0) {
                        _pos = offset;
                    }
                    break;
                case System.IO.SeekOrigin.Current:
                    if (_pos + offset >= 0) {
                        _pos += offset;
                    }
                    break;
                case System.IO.SeekOrigin.End:
                    long len = this.Length;
                    if (len + offset >= 0) {
                        _pos = len + offset;
                    }
                    break;
                default:
                    throw new NotSupportedException("Unidentified SeekOrigin argument");
            }
            Tracing.Log(Tracing.Debug,"Exit");
            return (long)_pos;
        }
    }
}

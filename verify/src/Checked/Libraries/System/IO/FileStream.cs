// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  FileStream
//
// Purpose: Exposes a Stream around a file, with full
// synchronous and asynchronous support, and buffering.
//
//===========================================================
#define BLACKHOLE

using System;
using System.Diagnostics;
using System.Threading;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace System.IO
{
    //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream"]/*' />
    public class FileStream : Stream
    {
        private MemFile file;
        private MemoryStream stream;

        internal FileStream(String path) {
            file = (MemFile) MemFileSystem.table[path];
            if (file == null) {
                file = new MemFile();
                file.data = new byte[0];
                MemFileSystem.table[path] = file;
            }
            byte[] data = file.data;
            stream = new MemoryStream(data.Length);
            stream.Write(data, 0, data.Length);
        }

        public FileStream(String path, FileMode mode): this(path) {}
        public FileStream(String path, FileMode mode, FileAccess access): this(path) {}
        public FileStream(String path, FileMode mode, FileAccess access, FileShare share): this(path) {}
        public FileStream(String path, FileMode mode, FileAccess access, FileShare share, int bufferSize): this(path) {}

        public override bool CanRead {
            get { return true; }
        }

        public override bool CanWrite {
            get { return true; }
        }

        public override bool CanSeek {
            get { return true; }
        }

        public override long Length {
            get { return stream.Length; }
        }

/*        
        public String Name {
            get { throw null; }
        }
*/

        public override long Position {
            get { return stream.Position; }
            set { stream.Position = value; }
        }

        public override void Close() {
            Flush();
        }
        
        protected virtual void Dispose(bool disposing) {
            Flush();
        }

        ~FileStream() {
            Flush();
        }

        public override void Flush() {
            file.data = stream.ToArray();
        }

        public override void SetLength(long value) {
            stream.SetLength(value);
        }
       
        public override int Read(byte[] array, int offset, int count) {
            return stream.Read(array, offset, count);
        }
        
        public override long Seek(long offset, SeekOrigin origin) {
            return stream.Seek(offset, origin);
        }
        
        public override void Write(byte[] array, int offset, int count) {
            stream.Write(array, offset, count);
        }
    }
}

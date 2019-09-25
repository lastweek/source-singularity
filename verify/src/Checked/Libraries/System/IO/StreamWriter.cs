// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  StreamWriter
//
// Purpose: For writing text to streams in a particular
// encoding.
//
//===========================================================  
using System;
using System.Diagnostics;
using System.Text;

namespace System.IO
{
    // This class implements a TextWriter for writing characters to a Stream.
    // This is designed for character output in a particular Encoding,
    // whereas the Stream class is designed for byte input and output.
    //
    //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter"]/*' />
    public class StreamWriter : TextWriter
    {
        // For UTF-8, the values of 1K for the default buffer size and 4K for the
        // file stream buffer size are reasonable & give very reasonable
        // performance for in terms of construction time for the StreamWriter and
        // write perf.  Note that for UTF-8, we end up allocating a 4K byte buffer,
        // which means we take advantage of the adaptive buffering code.
        // The performance using UnicodeEncoding is acceptable.
        private const int DefaultBufferSize = 1024;   // char[]
        private const int DefaultFileStreamBufferSize = 4096;
        private const int MinBufferSize = 128;

#if DONT
        // Bit bucket - Null has no backing store.
        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Null"]/*' />
        public new static readonly StreamWriter Null = new StreamWriter(Stream.Null, new UTF8Encoding(false, true), 128);
#endif

        internal Stream stream;
        private Encoding encoding;
        private Encoder encoder;
        internal byte[] byteBuffer;
        internal char[] charBuffer;
        internal int charPos;
        internal int charLen;
        internal bool autoFlush;
        private bool haveWrittenPreamble;
        private bool closable;  // For Console.Out - should Finalize call Dispose?

#if _DEBUG
        private String allocatedFrom = String.Empty;
#endif

        [Microsoft.Contracts.NotDelayed]
        internal StreamWriter() {
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.StreamWriter"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public StreamWriter(Stream stream)
            : this(stream, new UTF8Encoding(false, true), DefaultBufferSize) {
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.StreamWriter1"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public StreamWriter(Stream stream, Encoding encoding)
            : this(stream, encoding, DefaultBufferSize) {
        }

        // Creates a new StreamWriter for the given stream.  The
        // character encoding is set by encoding and the buffer size,
        // in number of 16-bit characters, is set by bufferSize.
        //
        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.StreamWriter2"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public StreamWriter(Stream stream, Encoding encoding, int bufferSize) {
            if (stream == null || encoding == null)
                throw new ArgumentNullException((stream==null ? "stream" : "encoding"));
            if (!stream.CanWrite)
                throw new ArgumentException("Argument_StreamNotWritable");
            if (bufferSize <= 0) throw new ArgumentOutOfRangeException("ArgumentOutOfRange_NeedPosNum");

            Init(stream, encoding, bufferSize);
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.StreamWriter3"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public StreamWriter(String path)
            : this(path, false, new UTF8Encoding(false, true), DefaultBufferSize) {
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.StreamWriter4"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public StreamWriter(String path, bool append)
            : this(path, append, new UTF8Encoding(false, true), DefaultBufferSize) {
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.StreamWriter5"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public StreamWriter(String path, bool append, Encoding encoding)
            : this(path, append, encoding, DefaultBufferSize) {
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.StreamWriter6"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public StreamWriter(String path, bool append, Encoding encoding, int bufferSize) {
            if (path == null || encoding == null)
                throw new ArgumentNullException((path==null ? "path" : "encoding"));
            if (bufferSize <= 0) throw new ArgumentOutOfRangeException("ArgumentOutOfRange_NeedPosNum");

            Stream stream = CreateFile(path, append);
            Init(stream, encoding, bufferSize);
        }

        private void Init(Stream stream, Encoding encoding, int bufferSize)
        {
            this.stream = stream;
            this.encoding = encoding;
            this.encoder = encoding.GetEncoder();
            if (bufferSize < MinBufferSize) bufferSize = MinBufferSize;
            charBuffer = new char[bufferSize];
            byteBuffer = new byte[encoding.GetMaxByteCount(bufferSize)];
            charLen = bufferSize;
            // If we're appending to a Stream that already has data, don't write
            // the preamble junk.
            if (stream.CanSeek && stream.Position > 0)
                haveWrittenPreamble = true;
            closable = true;
        }

        private static Stream CreateFile(String path, bool append) {
            FileMode mode = append? FileMode.Append: FileMode.Create;
            FileStream f = new FileStream(path, mode, FileAccess.Write, FileShare.Read, DefaultFileStreamBufferSize);
            return f;
        }


        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Close"]/*' />
        public override void Close() {
            Dispose(true);
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Dispose"]/*' />
        protected override void Dispose(bool disposing) {
            // Dispose of our resources if this StreamWriter is closable.
            // Note that Console.Out should not be closable.
            if (disposing) {
                if (stream != null) {
                    Flush(true, true);
                    if (Closable)
                        stream.Close();
                }
            }
            if (Closable && stream != null) {
                stream = null;
                byteBuffer = null;
                charBuffer = null;
                encoding = null;
                encoder = null;
                charLen = 0;
                base.Dispose(disposing);
            }
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Finalize"]/*' />
        ~StreamWriter()
        {
            // Make sure people closed this StreamWriter, but of course, make
            // allowances for BufferedStream (used by Console.Out & Error) and
            // StreamWriter::Null.
#if _DEBUG
            Debug.Correctness(charPos == 0, "You didn't close a StreamWriter, and you lost data!\r\nStream type: "+(stream==null ? "<null>" : stream.GetType().FullName)+((stream != null && stream is FileStream) ? "  File name: "+((FileStream)stream).NameInternal : "")+"\r\nAllocated from:\r\n"+allocatedFrom);
#endif
            Dispose(false);
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Flush"]/*' />
        public override void Flush() {
            Flush(true, true);
        }

        private void Flush(bool flushStream, bool flushEncoder) {
            // flushEncoder should be true at the end of the file and if
            // the user explicitly calls Flush (though not if AutoFlush is true).
            // This is required to flush any dangling characters from our UTF-7
            // and UTF-8 encoders.
            if (stream == null)
                __Error.WriterClosed();

            // Perf boost for Flush on non-dirty writers.
            if (charPos == 0 && !flushStream && !flushEncoder)
                return;

            if (!haveWrittenPreamble) {
                haveWrittenPreamble = true;
                byte[] preamble = encoding.GetPreamble();
                if (preamble.Length > 0)
                    stream.Write(preamble, 0, preamble.Length);
            }

            int count = encoder.GetBytes(charBuffer, 0, charPos, byteBuffer, 0, flushEncoder);
            charPos = 0;
            if (count > 0)
                stream.Write(byteBuffer, 0, count);
            // By definition, calling Flush should flush the stream, but this is
            // only necessary if we passed in true for flushStream.  The Web
            // Services guys have some perf tests where flushing needlessly hurts.
            if (flushStream)
                stream.Flush();
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.AutoFlush"]/*' />
        public virtual bool AutoFlush {
            get { return autoFlush; }
            set {
                autoFlush = value;
                if (value) Flush(true, false);
            }
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.BaseStream"]/*' />
        public virtual Stream BaseStream {
            get { return stream; }
        }

        internal bool Closable {
            get { return closable; }
            set { closable = value; }
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Encoding"]/*' />
        public override Encoding Encoding {
            get { return encoding; }
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Write"]/*' />
        public override void Write(char value) {
            if (charPos == charLen) Flush(false, false);
            charBuffer[charPos++] = value;
            if (autoFlush) Flush(true, false);
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Write1"]/*' />
        public override void Write(char[] buffer) {
            if (buffer == null) {
                return;
            }
            int index = 0;
            int count = buffer.Length;
            while (count > 0) {
                int limit = this.charLen - this.charPos;
                if (limit <= 0) {
                    this.Flush(false, false);
                    limit = this.charLen - this.charPos;
                }
                if (limit > count) {
                    limit = count;
                }
                Buffer.BlockCopy(buffer, index*2,
                                         charBuffer, charPos*2,
                                         limit*2);
                this.charPos += limit;
                index += limit;
                count -= limit;
            }
            if (this.autoFlush) {
                this.Flush(true, false);
            }
        }


        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Write2"]/*' />
        public override void Write(char[] buffer, int index, int count) {
            if (buffer == null) {
                throw new ArgumentNullException("buffer", "Buffer is null");
            }
            if (index < 0) {
                throw new ArgumentOutOfRangeException("index", "index is negative");
            }
            if (count < 0) {
                throw new ArgumentOutOfRangeException("count", "count is negative");
            }
            if (buffer.Length < index + count) {
                throw new ArgumentException("index + count greater than buffer length");
            }
            while (count > 0) {
                int limit = this.charLen - this.charPos;
                if (limit <= 0) {
                    this.Flush(false, false);
                    limit = this.charLen - this.charPos;
                }
                if (limit > count) {
                    limit = count;
                }
                for (int i = 0; i < limit; i++) {
                    charBuffer[this.charPos + i] = buffer[index + i];
                }
                this.charPos += limit;
                index += limit;
                count -= limit;
            }
            if (this.autoFlush) {
                this.Flush(true, false);
            }
        }

        //| <include file='doc\StreamWriter.uex' path='docs/doc[@for="StreamWriter.Write3"]/*' />
        public override void Write(String value) {
            if (value != null) {
                int count = value.Length;
                int index = 0;
                while (count > 0) {
                    if (charPos == charLen) Flush(false, false);
                    int n = charLen - charPos;
                    if (n > count) n = count;
                    Debug.Assert(n > 0, "StreamWriter::Write(String) isn't making progress!  This is most likely a race condition in user code.");
                    value.CopyTo(index, charBuffer, charPos, n);
                    charPos += n;
                    index += n;
                    count -= n;
                }
                if (autoFlush) Flush(true, false);
            }
        }

        //
        //// This method is more efficient for long strings outputted to streams
        //// than the one on TextWriter, and won't cause any problems in terms of
        //// hiding methods on TextWriter as long as languages respect the
        //// hide-by-name-and-sig metadata flag.
        //public override void WriteLine(String value) {
        //if (value != null) {
        //int count = value.Length;
        //int index = 0;
        //while (count > 0) {
        //if (charPos == charLen) Flush(false);
        //int n = charLen - charPos;
        //if (n > count) n = count;
        //Debug.Assert(n > 0, "StreamWriter::WriteLine(String) isn't making progress!  This is most likely a race condition in user code.");
        //value.CopyTo(index, charBuffer, charPos, n);
        //charPos += n;
        //index += n;
        //count -= n;
        //}
        //}
        //if (charPos >= charLen - 2) Flush(false);
        //Buffer.BlockCopy(CoreNewLine, 0, charBuffer, charPos*2, CoreNewLine.Length * 2);
        //charPos += CoreNewLine.Length;
        //if (autoFlush) Flush(true, false);
        //}
        //
    }
}

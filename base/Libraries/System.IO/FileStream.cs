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
using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.FileSystem;
using Microsoft.Singularity.V1.Services;
using FileSystem.Utils;
//
// Implementation notes:
//
// I've added buffering into FileStream as well.  I folded in the
// code from BufferedStream, so all the comments about it being mostly
// aggressive (and the possible perf improvement) apply to FileStream as
// well.
//
// Class Invariants:
// The class has one buffer, shared for reading & writing.  It can only be
// used for one or the other at any point in time - not both.  The following
// should be true:
//   0 <= _readPos <= _readLen < _bufferSize
//   0 <= _writePos < _bufferSize
//   _readPos == _readLen && _readPos > 0 implies the read buffer is valid,
//     but we're at the end of the buffer.
//   _readPos == _readLen == 0 means the read buffer contains garbage.
//   Either _writePos can be greater than 0, or _readLen & _readPos can be
//     greater than zero, but neither can be greater than zero at the same time.
//

namespace System.IO
{
    //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream"]/*' />
    public class FileStream : Stream
    {
        internal const int DefaultBufferSize = 4096;
        private TRef<FileContract.Imp:Ready> _imp;
        private byte[] _buffer;   // Shared read/write buffer.  Alloc on first use.
        private String _fileName; // Fully qualified file name.
        private bool _canRead;
        private bool _canWrite;
        private bool _canSeek;
        private bool _disposed;
#if BLACKHOLE
        private bool _isBlackHole;// Absorbs writes and gives nothing back.
#endif
        private int _readPos;     // Read pointer within shared buffer.
        private int _readLen;     // Number of bytes read in buffer from file.
        private int _writePos;    // Write pointer within shared buffer.
        private int _bufferSize;  // Length of internal buffer, if it's allocated.
        private long _pos;        // Cache current location in the file.
        private long _len;

        private IntPtr _handle;
        private long _appendStart;// When appending, prevent overwriting file.

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.FileStream"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public FileStream(DirectoryServiceContract.Imp:Ready! dsRoot, String path, FileMode mode)
            : this(dsRoot, path, mode, (mode == FileMode.Append ? FileAccess.Write : FileAccess.ReadWrite), FileShare.Read, DefaultBufferSize, Path.GetFileName(path), false) {
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.FileStream"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public FileStream(String path, FileMode mode)
        {
            DirectoryServiceContract.Imp dsRoot = DirectoryService.NewClientEndpoint();
            this(dsRoot, path, mode, (mode == FileMode.Append ? FileAccess.Write : FileAccess.ReadWrite), FileShare.Read, DefaultBufferSize, Path.GetFileName(path), false);
            delete dsRoot;
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.FileStream1"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public FileStream(DirectoryServiceContract.Imp:Ready! dsRoot, String path, FileMode mode, FileAccess access)
            : this(dsRoot, path, mode, access, FileShare.Read, DefaultBufferSize, Path.GetFileName(path), false) {
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.FileStream1"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public FileStream(String path, FileMode mode, FileAccess access)
        {
            DirectoryServiceContract.Imp dsRoot = DirectoryService.NewClientEndpoint();
            this(dsRoot, path, mode, access, FileShare.Read, DefaultBufferSize, Path.GetFileName(path), false);
            delete dsRoot;
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.FileStream2"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public FileStream(String path, FileMode mode, FileAccess access, FileShare share)
        {
            DirectoryServiceContract.Imp dsRoot = DirectoryService.NewClientEndpoint();
            this(dsRoot, path, mode, access, share, DefaultBufferSize, Path.GetFileName(path), false);
            delete dsRoot;
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.FileStream3"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public FileStream(String path, FileMode mode, FileAccess access, FileShare share, int bufferSize)
        {
            DirectoryServiceContract.Imp dsRoot = DirectoryService.NewClientEndpoint();
            this(dsRoot, path, mode, access, share, bufferSize, Path.GetFileName(path), false);
            delete dsRoot;
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.FileStream3"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public FileStream(DirectoryServiceContract.Imp:Ready! dsRoot, String path, FileMode mode, FileAccess access, FileShare share, int bufferSize)
            : this(dsRoot, path, mode, access, share, bufferSize, Path.GetFileName(path), false) {
        }

        [Microsoft.Contracts.NotDelayed]
        internal FileStream(DirectoryServiceContract.Imp:Ready! dsRoot, String path, FileMode mode, FileAccess access, FileShare share, int bufferSize, String msgPath, bool bFromProxy)
        {
            // Note: msgPath must be safe to hand back to untrusted code.

            _fileName = msgPath;  // To handle odd cases of finalizing partially constructed objects.

            if (path == null)
                throw new ArgumentNullException("path", "ArgumentNull_Path");
            if (path.Length == 0)
                throw new ArgumentException("Argument_EmptyPath");
            if (mode < FileMode.CreateNew || mode > FileMode.Append ||
                access < FileAccess.Read || access > FileAccess.ReadWrite ||
                share < FileShare.None || share > FileShare.ReadWrite) {
                String badArg = "mode";
                if (access < FileAccess.Read || access > FileAccess.ReadWrite)
                    badArg = "access";
                if (share < FileShare.None || share > FileShare.ReadWrite)
                    badArg = "share";
                throw new ArgumentOutOfRangeException(badArg, "ArgumentOutOfRange_Enum");
            }
            if (bufferSize <= 0)
                throw new ArgumentOutOfRangeException("bufferSize", "ArgumentOutOfRange_NeedPosNum");

            path = Path.GetFullPath(path);
#if false // uncomment to debug file access.
            Console.WriteLine("FileStream({0})", path);
#endif

            _fileName = path;
            FileAttributesRecord fileAttributes;
            ErrorCode error;
            FileUtils.GetAttributes(path, dsRoot, out fileAttributes, out error);
            _len = fileAttributes.FileSize;

            // Build up security permissions required, as well as validate we
            // have a sensible set of parameters.  IE, creating a brand new file
            // for reading doesn't make much sense.
            if ((access & FileAccess.Read) != 0) {
                if (mode == FileMode.Append)
                    throw new ArgumentException("Argument_InvalidAppendMode");
            }

#if BLACKHOLE
            if (error == ErrorCode.NotFound &&
                (access & FileAccess.Write) != 0 &&
                path.StartsWith("/blackhole/")) {
                // We only hand the case where attempting to write to
                // a non-existent file, in which we create a block hole for
                // Bartok.

                _canRead = (access & FileAccess.Read) != 0;
                _canWrite = (access & FileAccess.Write) != 0;
                _canSeek = true;
                _pos = 0;
                _bufferSize = bufferSize;
                _readPos = 0;
                _readLen = 0;
                _writePos = 0;
                _appendStart = -1;
                _isBlackHole = true;

                return;
            }
#endif

            // I can't think of any combos of FileMode we should disallow if we
            // don't have read access.  Writing would pretty much always be valid
            // in those cases.
            if ((access & FileAccess.Write) != 0) {
            }
            else {
                // No write access
                if (mode == FileMode.Truncate || mode == FileMode.CreateNew || mode == FileMode.Create || mode == FileMode.Append)
                    throw new ArgumentException(String.Format("Argument_InvalidFileMode&AccessCombo", mode, access));
            }

            bool seekToEnd = (mode == FileMode.Append);
            // Must use a valid Win32 constant here...
            if (mode == FileMode.Append)
                mode = FileMode.OpenOrCreate;

            ErrorCode errorCode;
            if (mode == FileMode.CreateNew || mode == FileMode.Create) {
                if (File.Exists(path)) {
                    if (mode == FileMode.CreateNew) {
                        __Error.WinIOError(__Error.ERROR_FILE_EXISTS, path);
                        assume false;
                    }
                    File.Delete(path);
                }
                if (FileUtils.CreateFile(path, out errorCode) != 0) {
#if false
                    Console.WriteLine("FileUtils.CreateFile({0}) failed. Error={1}", path, SdsUtils.ErrorCodeToString(errorCode));
#endif
                    if (mode == FileMode.Create) {
                        __Error.WinIOError(-1, _fileName);
                        assume false; // never get here
                    }
                }
            }

            FileContract.Imp fi = FileUtils.OpenFile(path, dsRoot, out error);
            if (error != ErrorCode.NoError || fi == null) {
#if false
                Console.WriteLine("FileUtils.OpenFile({0}, out {1})",
                                  path, (int)error);
#endif
                // Return a meaningful error, using the RELATIVE path to
                // the file to avoid returning extra information to the caller
                // unless they have path discovery permission, in which case
                // the full path is fine & useful.
                __Error.WinIOError((int)error, _fileName);
                assume false; // never get here
            }


            _imp = new TRef<FileContract.Imp:Ready>(fi);
            _canRead = (access & FileAccess.Read) != 0;
            _canWrite = (access & FileAccess.Write) != 0;
            _canSeek = true;
            _pos = 0;
            _bufferSize = bufferSize;
            _readPos = 0;
            _readLen = 0;
            _writePos = 0;

            // For Append mode...
            if (seekToEnd) {
                _appendStart = SeekCore(0, SeekOrigin.End);
            }
            else {
                _appendStart = -1;
            }
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.CanRead"]/*' />
        public override bool CanRead {
            get { return _canRead; }
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.CanWrite"]/*' />
        public override bool CanWrite {
            get { return _canWrite; }
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.CanSeek"]/*' />
        public override bool CanSeek {
            get { return _canSeek; }
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Length"]/*' />
        public override long Length {
            get {
                if (!CanSeek) __Error.SeekNotSupported();
#if false
                long len = 0;
#else
                long len = Native.GetFileSize(_handle);
#endif

                // If we're writing near the end of the file, we must include our
                // internal buffer in our Length calculation.
                if (_writePos > 0 && _pos + _writePos > len)
                    len = _writePos + _pos;
                return len;
            }
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Name"]/*' />
        public String Name {
            get {
                if (_fileName == null)
                    return "IO_UnknownFileName";
                return _fileName;
            }
        }

        internal String NameInternal {
            get {
                if (_fileName == null)
                    return "<UnknownFileName>";
                return _fileName;
            }
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Position"]/*' />
        public override long Position {
            get {
                if (!CanSeek) __Error.SeekNotSupported();
                Debug.Assert((_readPos==0 && _readLen==0 && _writePos >= 0) || (_writePos==0 && _readPos <= _readLen), "We're either reading or writing, but not both.");

                return _pos + (_readPos - _readLen + _writePos);
            }
            set {
                if (value < 0) throw new ArgumentOutOfRangeException("value", "ArgumentOutOfRange_NeedNonNegNum");
                if (_writePos > 0) FlushWrite();
                _readPos = 0;
                _readLen = 0;
                Seek(value, SeekOrigin.Begin);
            }
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Close"]/*' />
        public override void Close()
        {
            Dispose(true);
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Dispose"]/*' />
        protected virtual void Dispose(bool disposing)
        {
            // Nothing will be done differently based on whether we are
            // disposing vs. finalizing.
#if false
            if (_handle != IntPtr.Zero) {
                Flush();
                _handle = IntPtr.Zero;
            }
#endif

            if (_disposed == false && _isBlackHole == false) {
                // NB black has no associated imp.
                FileContract.Imp fi = _imp.Acquire();
                delete fi;

                _canRead  = false;
                _canWrite = false;
                _canSeek  = false;
                _buffer   = null;
                _disposed = true;
            }
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Finalize"]/*' />
        ~FileStream()
        {
#if false
            if (_handle != IntPtr.Zero) {
                Dispose(false);
            }
#endif
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Flush"]/*' />
        public override void Flush()
        {
            if (_writePos > 0) {
                FlushWrite();
            }
            else if (_readPos < _readLen && CanSeek) {
                FlushRead();
            }
        }

        // Reading is done by blocks from the file, but someone could read
        // 1 byte from the buffer then write.  At that point, the OS's file
        // pointer is out of sync with the stream's position.  All write
        // functions should call this function to preserve the position in the file.
        private void FlushRead() {
            Debug.Assert(_writePos == 0, "FileStream: Write buffer must be empty in FlushRead!");
            if (_readPos - _readLen != 0)
                SeekCore(_readPos - _readLen, SeekOrigin.Current);
            _readPos = 0;
            _readLen = 0;
        }

        // Writes are buffered.  Anytime the buffer fills up
        // (_writePos + delta > _bufferSize) or the buffer switches to reading
        // and there is dirty data (_writePos > 0), this function must be called.
        private void FlushWrite() {
            Debug.Assert(_readPos == 0 && _readLen == 0, "FileStream: Read buffer must be empty in FlushWrite!");
            WriteCore(_buffer, 0, _writePos);
            _writePos = 0;
        }


        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.SetLength"]/*' />
        public override void SetLength(long value)
        {
            if (value < 0)
                throw new ArgumentOutOfRangeException("value", "ArgumentOutOfRange_NeedNonNegNum");
            if (!CanSeek) __Error.SeekNotSupported();
            if (!CanWrite) __Error.WriteNotSupported();
            // Handle buffering updates.
            if (_writePos > 0) {
                FlushWrite();
            }
            else if (_readPos < _readLen) {
                FlushRead();
            }
            if (_appendStart != -1 && value < _appendStart)
                throw new IOException("IO.IO_SetLengthAppendTruncate");
            long origPos = _pos;
            if (_pos != value)
                SeekCore(value, SeekOrigin.Begin);
#if false
            if (!Native.SetEndOfFile(_handle)) {
                __Error.WinIOError(0, String.Empty);
            }
#endif
            // Return file pointer to where it was before setting length
            if (origPos != value) {
                if (origPos < value)
                    SeekCore(origPos, SeekOrigin.Begin);
                else
                    SeekCore(0, SeekOrigin.End);
            }
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Read"]/*' />
        public override int Read([In, Out] byte[] array, int offset, int count) {
            if (array == null)
                throw new ArgumentNullException("array", "ArgumentNull_Buffer");
            if (offset < 0)
                throw new ArgumentOutOfRangeException("offset", "ArgumentOutOfRange_NeedNonNegNum");
            if (count < 0)
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_NeedNonNegNum");
            if (array.Length - offset < count)
                throw new ArgumentException("Argument_InvalidOffLen");


            Debug.Assert((_readPos==0 && _readLen==0 && _writePos >= 0) || (_writePos==0 && _readPos <= _readLen), "We're either reading or writing, but not both.");

            bool isBlocked = false;
            int n = _readLen - _readPos;
            // if the read buffer is empty, read into either user's array or our
            // buffer, depending on number of bytes user asked for and buffer size.
            if (n == 0) {
                if (!CanRead) __Error.ReadNotSupported();
                if (_writePos > 0) FlushWrite();
                if (count >= _bufferSize) {
                    n = ReadCore(array, offset, count);
                    // Throw away read buffer.
                    _readPos = 0;
                    _readLen = 0;
                    return n;
                }
                if (_buffer == null) _buffer = new byte[_bufferSize];
                n = ReadCore(_buffer, 0, _bufferSize);
                if (n == 0) return 0;
                isBlocked = n < _bufferSize;
                _readPos = 0;
                _readLen = n;
            }
            // Now copy min of count or numBytesAvailable (ie, near EOF) to array.
            if (n > count) n = count;
            Buffer.BlockCopy(_buffer, _readPos, array, offset, n);
            _readPos += n;

            // If we hit the end of the buffer and didn't have enough bytes, we must
            // read some more from the underlying stream.  However, if we got
            // fewer bytes from the underlying stream than we asked for (ie, we're
            // probably blocked), don't ask for more bytes.
            if (n < count && !isBlocked) {
                Debug.Assert(_readPos == _readLen, "Read buffer should be empty!");
                int moreBytesRead = ReadCore(array, offset + n, count - n);
                n += moreBytesRead;
                // We've just made our buffer inconsistent with our position
                // pointer.  We must throw away the read buffer.
                _readPos = 0;
                _readLen = 0;
            }

            return n;
        }

        private int ReadCore(byte[] buffer, int offset, int count) {
            Debug.Assert(CanRead, "CanRead");
            Debug.Assert(_writePos == 0, "_writePos == 0");

#if BLACKHOLE
            if (_isBlackHole) {
                return 0;
            }
#endif

            FileContract.Imp fi = _imp.Acquire();
#if false
            Console.WriteLine("ReadCore(offset={0}, count={1}, _pos={2}/{3})",
                              offset, count, _pos, _len);
            if (offset != 0) {
                DebugStub.Break();
            }
#endif
            long r = FileUtils.Read(fi, offset, count, _pos, (!)buffer);
            if (r == -1) {
                __Error.WinIOError(1, String.Empty);
            }
#if false // uncomment to debug file access.
            Console.WriteLine("  {0:x2}{1:x2}{2:x2}{3:x2} {4:x2}{5:x2}{6:x2}{7:x2}" +
                              " {8:x2}{9:x2}{10:x2}{11:x2} {12:x2}{13:x2}{14:x2}{15:x2}",
                              (byte)(r > 0 ? buffer[0] : (byte)0),
                              (byte)(r > 1 ? buffer[1] : (byte)0),
                              (byte)(r > 2 ? buffer[2] : (byte)0),
                              (byte)(r > 3 ? buffer[3] : (byte)0),
                              (byte)(r > 4 ? buffer[4] : (byte)0),
                              (byte)(r > 5 ? buffer[5] : (byte)0),
                              (byte)(r > 6 ? buffer[6] : (byte)0),
                              (byte)(r > 7 ? buffer[7] : (byte)0),
                              (byte)(r > 8 ? buffer[8] : (byte)0),
                              (byte)(r > 9 ? buffer[9] : (byte)0),
                              (byte)(r > 10 ? buffer[10] : (byte)0),
                              (byte)(r > 11 ? buffer[11] : (byte)0),
                              (byte)(r > 12 ? buffer[12] : (byte)0),
                              (byte)(r > 13 ? buffer[13] : (byte)0),
                              (byte)(r > 14 ? buffer[14] : (byte)0),
                              (byte)(r > 15 ? buffer[15] : (byte)0));
#endif
            _imp.Release(fi);
            _pos += r;

            return (int)r;
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Seek"]/*' />
        public override long Seek(long offset, SeekOrigin origin) {
            if (origin < SeekOrigin.Begin || origin > SeekOrigin.End)
                throw new ArgumentException("Argument_InvalidSeekOrigin");
            if (!CanSeek) __Error.SeekNotSupported();

            Debug.Assert((_readPos==0 && _readLen==0 && _writePos >= 0) || (_writePos==0 && _readPos <= _readLen), "We're either reading or writing, but not both.");

            // If we've got bytes in our buffer to write, write them out.
            // If we've read in and consumed some bytes, we'll have to adjust
            // our seek positions ONLY IF we're seeking relative to the current
            // position in the stream.  This simulates doing a seek to the new
            // position, then a read for the number of bytes we have in our buffer.
            if (_writePos > 0) {
                FlushWrite();
            }
            else if (origin == SeekOrigin.Current) {
                // Don't call FlushRead here, which would have caused an infinite
                // loop.  Simply adjust the seek origin.  This isn't necessary
                // if we're seeking relative to the beginning or end of the stream.
                offset -= (_readLen - _readPos);
            }

            long oldPos = _pos + (_readPos - _readLen);
            long pos = SeekCore(offset, origin);

            // Prevent users from overwriting data in a file that was opened in
            // append mode.
            if (_appendStart != -1 && pos < _appendStart) {
                SeekCore(oldPos, SeekOrigin.Begin);
                throw new IOException("IO.IO_SeekAppendOverwrite");
            }

            // We now must update the read buffer.  We can in some cases simply
            // update _readPos within the buffer, copy around the buffer so our
            // Position property is still correct, and avoid having to do more
            // reads from the disk.  Otherwise, discard the buffer's contents.
            if (_readLen > 0) {
                // We can optimize the following condition:
                // oldPos - _readPos <= pos < oldPos + _readLen - _readPos
                if (oldPos == pos) {
                    if (_readPos > 0) {
                        //Console.WriteLine("Seek: seeked for 0, adjusting buffer back by: "+_readPos+"  _readLen: "+_readLen);
                        Buffer.BlockCopy(_buffer, _readPos, _buffer, 0, _readLen - _readPos);
                        _readLen -= _readPos;
                        _readPos = 0;
                    }
                    // If we still have buffered data, we must update the stream's
                    // position so our Position property is correct.
                    if (_readLen > 0)
                        SeekCore(_readLen, SeekOrigin.Current);
                }
                else if (oldPos - _readPos < pos && pos < oldPos + _readLen - _readPos) {
                    int diff = (int)(pos - oldPos);
                    //Console.WriteLine("Seek: diff was "+diff+", readpos was "+_readPos+"  adjusting buffer - shrinking by "+ (_readPos + diff));
                    Buffer.BlockCopy(_buffer, _readPos+diff, _buffer, 0, _readLen - (_readPos + diff));
                    _readLen -= (_readPos + diff);
                    _readPos = 0;
                    if (_readLen > 0)
                        SeekCore(_readLen, SeekOrigin.Current);
                }
                else {
                    // Lose the read buffer.
                    _readPos = 0;
                    _readLen = 0;
                }
                Debug.Assert(_readLen >= 0 && _readPos <= _readLen, "_readLen should be nonnegative, and _readPos should be less than or equal _readLen");
                Debug.Assert(pos == Position, "Seek optimization: pos != Position!  Buffer math was mangled.");
            }
            return pos;
        }

        // This doesn't do argument checking.  Necessary for SetLength, which must
        // set the file pointer beyond the end of the file.
        private long SeekCore(long offset, SeekOrigin origin) {
            Debug.Assert(origin>=SeekOrigin.Begin && origin<=SeekOrigin.End, "origin>=SeekOrigin.Begin && origin<=SeekOrigin.End");

#if false
            int hr = 0;
            long ret = 0;
            ret = Native.SetFilePointer(_handle, offset, origin);
            if (ret == -1) __Error.WinIOError(hr, String.Empty);
            _pos = ret;
            return ret;
#else
            // mostly ignores origin.
            if (origin == SeekOrigin.Begin) {
                _pos = offset;
            }
            else if (origin == SeekOrigin.Current) {
                _pos += offset;
            }
            else if (origin == SeekOrigin.End) {
                _pos = _len + offset;
            }
            return _pos;
#endif
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Write"]/*' />
        public override void Write(byte[] array, int offset, int count) {
            if (array == null)
                throw new ArgumentNullException("array", "ArgumentNull_Buffer");
            if (offset < 0)
                throw new ArgumentOutOfRangeException("offset", "ArgumentOutOfRange_NeedNonNegNum");
            if (count < 0)
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_NeedNonNegNum");
            if (array.Length - offset < count)
                throw new ArgumentException("Argument_InvalidOffLen");

            if (_writePos == 0) {
                // Ensure we can write to the stream, and ready buffer for writing.
                if (!CanWrite) __Error.WriteNotSupported();
                if (_readPos < _readLen) FlushRead();
                _readPos = 0;
                _readLen = 0;
            }

            // If our buffer has data in it, copy data from the user's array into
            // the buffer, and if we can fit it all there, return.  Otherwise, write
            // the buffer to disk and copy any remaining data into our buffer.
            // The assumption here is memcpy is cheaper than disk (or net) IO.
            // (10 milliseconds to disk vs. ~20-30 microseconds for a 4K memcpy)
            // So the extra copying will reduce the total number of writes, in
            // non-pathological cases (ie, write 1 byte, then write for the buffer
            // size repeatedly)
            if (_writePos > 0) {
                int numBytes = _bufferSize - _writePos;   // space left in buffer
                if (numBytes > 0) {
                    if (numBytes > count)
                        numBytes = count;
                    Buffer.BlockCopy(array, offset, _buffer, _writePos, numBytes);
                    _writePos += numBytes;
                    if (count == numBytes) return;
                    offset += numBytes;
                    count -= numBytes;
                }
                // Reset our buffer.  We essentially want to call FlushWrite
                // without calling Flush on the underlying Stream.
                WriteCore(_buffer, 0, _writePos);
                _writePos = 0;
            }
            // If the buffer would slow writes down, avoid buffer completely.
            if (count >= _bufferSize) {
                Debug.Assert(_writePos == 0, "FileStream cannot have buffered data to write here!  Your stream will be corrupted.");
                WriteCore(array, offset, count);
                return;
            }
            else if (count == 0)
                return;  // Don't allocate a buffer then call memcpy for 0 bytes.
            if (_buffer == null) _buffer = new byte[_bufferSize];
            // Copy remaining bytes into buffer, to write at a later date.
            Buffer.BlockCopy(array, offset, _buffer, _writePos, count);
            _writePos = count;
            return;
        }

        private void WriteCore(byte[]! buffer, int offset, int count) {
            Debug.Assert(CanWrite, "CanWrite");
            Debug.Assert(_readPos == _readLen, "_readPos == _readLen");

#if BLACKHOLE
            if (_isBlackHole) {
                _pos += count;
                return;
            }
#endif

            FileContract.Imp fi = _imp.Acquire();
            long r = FileUtils.Write(fi, offset, count, _pos, (!)buffer);
            _imp.Release(fi);
            if (r == -1) {
                __Error.WinIOError(1, String.Empty);
            }
            _pos += r;
            return;
        }

        // Reads a byte from the file stream.  Returns the byte cast to an int
        // or -1 if reading from the end of the stream.
        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.ReadByte"]/*' />
        public override int ReadByte() {
            if (_readLen == 0 && !CanRead) __Error.ReadNotSupported();
            Debug.Assert((_readPos==0 && _readLen==0 && _writePos >= 0) || (_writePos==0 && _readPos <= _readLen), "We're either reading or writing, but not both.");
            if (_readPos == _readLen) {
                if (_writePos > 0) FlushWrite();
                Debug.Assert(_bufferSize > 0, "_bufferSize > 0");
                if (_buffer == null) _buffer = new byte[_bufferSize];
                _readLen = ReadCore(_buffer, 0, _bufferSize);
                _readPos = 0;
            }
            if (_readPos == _readLen)
                return -1;

            return _buffer[_readPos++];
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.WriteByte"]/*' />
        public override void WriteByte(byte value)
        {
            if (_writePos == 0) {
                if (!CanWrite) __Error.WriteNotSupported();
                if (_readPos < _readLen) FlushRead();
                _readPos = 0;
                _readLen = 0;
                Debug.Assert(_bufferSize > 0, "_bufferSize > 0");
                if (_buffer == null) _buffer = new byte[_bufferSize];
            }
            if (_writePos == _bufferSize)
                FlushWrite();

            _buffer[_writePos++] = value;
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Lock"]/*' />
        public virtual void Lock(long position, long length) {
            if (position < 0 || length < 0)
                throw new ArgumentOutOfRangeException((position < 0 ? "position" : "length"), "ArgumentOutOfRange_NeedNonNegNum");

#if false
            if (!Native.LockFile(_handle, position, length))
                __Error.WinIOError();
#endif
        }

        //| <include file='doc\FileStream.uex' path='docs/doc[@for="FileStream.Unlock"]/*' />
        public virtual void Unlock(long position, long length) {
            if (position < 0 || length < 0)
                throw new ArgumentOutOfRangeException((position < 0 ? "position" : "length"), "ArgumentOutOfRange_NeedNonNegNum");

#if false
            if (!Native.UnlockFile(_handle, position, length))
                __Error.WinIOError();
#endif
        }
    }
}

// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Microsoft.Singularity.KernelDebugger
{
    /// <summary>
    /// This class allows the kernel to send/receive files to/from the attached kernel debugger,
    /// if any.  Currently, the only use for this is to support the ".kdfiles" command in KD.
    /// (Refer to the Windows Debugging Tools documentation (debugger.chm) for info on .kdfiles.)
    /// This allows developers to transfer program binaries (and other files) over the debugger
    /// port, rather than a filesystem, in order to speed up development.
    /// 
    /// In the comments in this file, 'host' refers to the machine running the kernel debugger.
    /// </summary>
    [NoCCtor]
    [CLSCompliant(false)]
    public class KernelDebuggerFiles
    {
        /// <summary>
        /// This method opens a file on the host.  This file handle can be used in calls to ReadHostFile,
        /// WriteHostFile (depending on access requested), and CloseHostFile.
        /// </summary>
        /// <param name="FileHandle">Returns the file handle.  This handle has meaning only to the host.</param>
        /// <param name="FileLength">Returns the length of the file.</param>
        /// 
        /// <param name="FileName">
        /// The file to open.  Note that KD will not allow the debug target to open arbitrary files; this method 
        /// can only be used to open files that have been added to the .kdfiles set by the developer controlling KD.
        /// For example, a .kdfiles file (say, kdfiles.txt) contains map entries, in this form:
        /// 
        /// map [from] [to]
        /// 
        /// This string identifies the "from" part.  The "to" part identifies some file in the namespace of
        /// the machine running KD.  If the file is opened successfully, then the debug target can read/write
        /// the file.
        /// </param>
        /// 
        /// <param name="DesiredAccess">
        /// The access mask requested, using standard Windows access masks.
        /// However, note that KD will only look for the FILE_READ_DATA and FILE_WRITE_DATA bits, which it
        /// maps to GENERIC_READ and GENERIC_WRITE.  So don't bother specifying any bits outside of those;
        /// they will be ignored.
        /// </param>
        /// 
        /// <param name="FileAttributes">Initial file attributes, if creating a file.  Most callers should pass 0.</param>
        /// 
        /// <param name="ShareAccess">
        /// The shared access mask, if any.  If opening a file for read access, then pass FILE_SHARE_READ.
        /// </param>
        /// 
        /// <param name="CreateDisposition">Specifies what to do if the file already exists, or doesn't.
        /// Use FILE_OPEN, FILE_CREATE, etc.
        /// </param>
        /// 
        /// <returns>True if the file was successfully opened.</returns>
        public static unsafe bool CreateHostFile(
            out long FileHandle,
            out long FileLength,
            string FileName,
            uint DesiredAccess,
            uint FileAttributes,
            uint ShareAccess,
            uint CreateDisposition)
        {
            FileHandle = 0;
            FileLength = 0;

            if (!Kd.IsDebuggerPresent()) {
                // Think about how silly it would be to call DebugStub.WriteLine here.
                return false;
            }

            int request_data_size = sizeof(char) * (FileName.Length + 1);
            if (request_data_size + sizeof(HostFileIoRequest) > Kd.MaxPacketSize) {
                Dbg("CreateHostFile: Filename is too long.");
                return false;
            }

            // The request data for "create file" consists of the filename,
            // in little-endian UTF-16, with a Unicode NUL terminator character.
            byte[] request_data = new byte[request_data_size];
            for (int i = 0; i < FileName.Length; i++) {
                char c = FileName[i];
                request_data[i * 2] = (byte)(c & 0xff);
                request_data[i * 2 + 1] = (byte)((c >> 8) & 0xff);
            }
            request_data[FileName.Length * 2] = 0;
            request_data[FileName.Length * 2 + 1] = 0;

            //
            // Send packet to the kernel debugger on the host machine.
            //

            HostFileIoRequest request = new HostFileIoRequest();
            request.ApiNumber = (uint)KdApi.CreateFile;
            request.CreateFile.DesiredAccess = DesiredAccess;
            request.CreateFile.FileAttributes = FileAttributes;
            request.CreateFile.ShareAccess = ShareAccess;
            request.CreateFile.CreateDisposition = CreateDisposition;
            request.CreateFile.CreateOptions = 0;

            HostFileIoResponse response;

            bool succeeded;
            int response_data_length;

            fixed (byte* request_data_pinned = &request_data[0])
            {
                succeeded = SendFileIoRequestWaitResponse(
                    request,
                    request_data_pinned,
                    request_data_size,
                    out response,
                    null,
                    0,
                    out response_data_length);
            }

            if (succeeded) {
                if (response.Status == 0) {
                    Dbg("Successfully opened KD file '{0}', handle 0x{1:x} length 0x{2:x}",
                        FileName, response.CreateFile.FileHandle, response.CreateFile.FileLength);
                    FileHandle = response.CreateFile.FileHandle;
                    FileLength = response.CreateFile.FileLength;
                    return true;
                }
                else {
                    Dbg("Failed to open KD file '{0}'.  NTSTATUS = 0x{1:x}.", FileName, response.Status);
                    return false;
                }
            }
            else {
                Dbg("Failed to open KD file '{0}'.", FileName);
                return false;
            }
        }

        /// <summary>
        /// Reads data from a host file that has already been opened using CreateHostFile.
        /// </summary>
        /// <param name="RemoteHandle">The file handle.</param>
        /// <param name="FileOffset">Offset within the file of the chunk to read.</param>
        /// <param name="Buffer">The buffer to store data into.</param>
        /// <param name="Length">The number of bytes to transfer.</param>
        /// <param name="BytesTransferred">On return, the number of bytes actually transferred.</param>
        /// <returns>True if the transfer succeeded.</returns>
        public static unsafe bool ReadHostFile(
            long RemoteHandle,
            long FileOffset,
            void* Buffer,
            int Length,
            out int BytesTransferred)
        {
            BytesTransferred = 0;

            if (!Kd.IsDebuggerPresent())
                return false;

            Dbg("ReadHostFile: Handle {0:x8} FileOffset {1:x8} Buffer {2:x8} Length {3:x8}",
                RemoteHandle,
                FileOffset,
                (UIntPtr)Buffer,
                Length);

            if (Length < 0) {
                throw new ArgumentOutOfRangeException("Length");
            }

            int transfer_size = Length;
            int MaxTransferSize = Kd.MaxPacketSize - 0x200; // sizeof(HostFileIoRequest);

            if (transfer_size > MaxTransferSize) {
                Dbg("ReadHostFile: Length exceeds max transfer size; truncating to 0x{0:x}", MaxTransferSize);
                transfer_size = MaxTransferSize;
            }

            HostFileIoRequest request = new HostFileIoRequest();
            request.ApiNumber = (uint)KdApi.ReadFile;
            request.ReadFile.FileHandle = RemoteHandle;
            request.ReadFile.FileOffset = FileOffset;
            request.ReadFile.Length = (uint)transfer_size;

            HostFileIoResponse response;

            int response_data_length;
            bool succeeded;

            succeeded = SendFileIoRequestWaitResponse(
                request,
                null,
                0,
                out response,
                (byte*)Buffer,
                transfer_size,
                out response_data_length);

            if (succeeded) {
                if (response.Status == 0) {
                    Dbg("Received DBGKD_READ_FILE.  Successfully transfered {0} bytes.", response.ReadFile.BytesTransferred);
                    BytesTransferred = (int)response.ReadFile.BytesTransferred;
                    return true;
                }
                else {
                    Dbg("Received DBGKD_READ_FILE, Status indicates failure.  Status = 0x{0:x8}", (uint)response.Status);
                    DebugStub.Break();
                    BytesTransferred = 0;
                    return false;
                }
            }
            else {
                Dbg("Failed to receive response to DBGKD_READ_FILE.");
                BytesTransferred = 0;
                return false;
            }
        }

        /// <summary>
        /// This internal method handles executing a host file I/O request.  All requests use the
        /// DBGKD_FILEIO structure; using a structure with a different length will greatly confuse
        /// the kernel debugger, the kernel, or both.
        /// </summary>
        /// 
        /// <param name="Request">The request to send to the debugger.</param>
        /// <param name="RequestDataBuffer">A buffer containing additional data, if any, to send with the request.</param>
        /// <param name="RequestDataLength">The length of the additional data to send, or zero if there is none.</param>
        /// <param name="Response">On return, contains the response message.</param>
        /// <param name="ResponseDataBuffer">A buffer which receives any returned with the response.</param>
        /// <param name="ResponseDataMaximumLength">The maximum length of the data to store in the response buffer.</param>
        /// <param name="ResponseDataActualLength">The actual length of the data to store in the response buffer.</param>
        /// <returns></returns>
        static unsafe bool SendFileIoRequestWaitResponse(
            HostFileIoRequest Request,
            byte* RequestDataBuffer,
            int RequestDataLength,
            out HostFileIoResponse Response,
            byte* ResponseDataBuffer,
            int ResponseDataMaximumLength,
            out int ResponseDataActualLength)
        {
            HostFileIoResponse local_response = new HostFileIoResponse();

            Kd.Lock();

            // Do NOT use Dbg() or DebugStub.WriteLine() while Kd.Lock() is in effect.

            bool result = Kd.SendRequestWaitResponse(
                KdPacketType.FileIo,
                (byte*)&Request,
                sizeof(HostFileIoRequest),
                RequestDataBuffer,
                RequestDataLength,
                (byte*)&local_response,
                sizeof(HostFileIoResponse),
                ResponseDataBuffer,
                ResponseDataMaximumLength,
                out ResponseDataActualLength);

            Kd.Unlock();

            Response = local_response;
            return result;
        }

        static bool _dbg_to_kdprint;

        static void Dbg(string line)
        {
            if (_dbg_to_kdprint)
                DebugStub.WriteLine("KdFiles.cs: " + line);
        }

        static void Dbg(string format, params object[] args)
        {
            Dbg(String.Format(format, args));
        }

        /// <summary>
        /// Writes data to a file open on the host.
        /// </summary>
        /// 
        /// <param name="FileHandle">The host file handle, acquired using CreateHostFile.</param>
        /// <param name="FileOffset">
        /// The offset within the file to begin writing.
        /// (TODO: Does this support NT-style always-append semantics?  Probably.)
        /// </param>
        /// <param name="Buffer">The buffer containing the data to write.</param>
        /// <param name="Length">The number of bytes to write.</param>
        /// <param name="BytesTransferred">The actual number of bytes transferred.</param>
        /// <returns>True if the transfer succeeded.</returns>
        public static unsafe bool WriteHostFile(
            long FileHandle,
            long FileOffset,
            void* Buffer,
            int Length,
            out int BytesTransferred)
        {
            BytesTransferred = 0;

            if (!Kd.IsDebuggerPresent())
                return false;

            if (Length < 0)
                throw new ArgumentOutOfRangeException("Length");

            int transfer_size = Math.Min(Length, Kd.MaxPacketSize - sizeof(HostFileIoRequest));

            HostFileIoRequest request = new HostFileIoRequest();
            request.ApiNumber = (uint)KdApi.WriteFile;
            request.WriteFile.FileHandle = FileHandle;
            request.WriteFile.FileOffset = FileOffset;
            request.WriteFile.Length = (uint)transfer_size;

            HostFileIoResponse response;

            //
            // Send packet to the kernel debugger on the host machine.
            //

            int response_data_length;

            bool succeeded = SendFileIoRequestWaitResponse(
                request, 
                (byte*)Buffer, 
                Length,
                out response,
                null,
                0,
                out response_data_length
                );

            if (succeeded) {
                if (response.Status == 0) {
                    Dbg("Successfully wrote {0} bytes to host file.", response.WriteFile.BytesTransferred);
                    return true;
                }
                else {
                    Dbg("Received response to 'write file' request, but it indicates failure.");
                    return false;
                }
            }
            else {
                Dbg("Received response to 'write file' request, but it indicates failure.");
                return false;
            }
        }


        /// <summary>
        /// Closes a file handle that was opened using CreateHostFile.
        /// </summary>
        /// <param name="FileHandle">The file handle to close.</param>
        public unsafe static void CloseHostFile(long FileHandle)
        {
            if (!Kd.IsDebuggerPresent())
                return;

            Dbg("Closing file handle 0x{0:x}", FileHandle);

            HostFileIoRequest request = new HostFileIoRequest();
            request.ApiNumber = (uint)KdApi.CloseFile;
            request.CloseFile.FileHandle = FileHandle;

            HostFileIoResponse response;
            int response_data_length;
            bool succeeded = SendFileIoRequestWaitResponse(
                request,
                null,
                0,
                out response,
                null,
                0,
                out response_data_length);

            if (succeeded) {
                if (response.Status == 0) {
                    Dbg("Successfully closed host file handle.");
                }
                else {
                    Dbg("Received response to DBGKD_CLOSE_FILE, but it indicates error.  NTSTATUS: 0x{0:x8}", response.Status);
                }
            }
            else {
                Dbg("Failed to receive packet for response to DBGKD_CLOSE_FILE");
            }
        }


        #region NT definitions for KDBG_CREATE_FILE
        // These values are stored in the KDBG_CREATE_FILE structure, when the debuggee asks
        // to open a file on the host (the machine running WinDbg/KD (aka DbgEng)).
        // These use the NT values, not Win32 API values.

        // Values for AccessMask.
        // The ONLY bits (in the access mask) that DbgEng cares about are FILE_READ_DATA and FILE_WRITE_DATA,
        // which internally DbgEng translates into GENERIC_READ and GENERIC_WRITE.  DbgEng does not just
        // pass these values directly to CreateFile.

        public const uint FILE_READ_DATA = 0x0001;
        public const uint FILE_WRITE_DATA = 0x0002;

        // Values for FileShare.  Passed unmodified to CreateFile.
        public const uint FILE_SHARE_READ = 1;
        public const uint FILE_SHARE_WRITE = 2;
        public const uint FILE_SHARE_DELETE = 4;

        // Values for CreateDisposition.  Translated into Win32 equivalents by DbgEng.
        public const uint FILE_SUPERSEDE    = 0x00000000;
        public const uint FILE_OPEN         = 0x00000001;
        public const uint FILE_CREATE       = 0x00000002;
        public const uint FILE_OPEN_IF      = 0x00000003;
        public const uint FILE_OVERWRITE    = 0x00000004;
        public const uint FILE_OVERWRITE_IF = 0x00000005;

        #endregion

        /// <summary>
        /// Transfers a file from the debugger to local memory.  See CreateHostFile for more info.
        /// </summary>
        /// <param name="filename">
        /// The file to download; this filename has meaning only to the host debugger.
        /// </param>
        /// <param name="FileData"></param>
        /// <returns></returns>
        public unsafe static bool DownloadHostFile(string filename, out byte[] FileData)
        {
            FileData = null;

            if (!Kd.IsDebuggerPresent())
                return false;

            long FileHandle;
            long FileLength64;

            Dbg("Requesting file '{0}' from debugger", filename);

            bool create_result = CreateHostFile(
                out FileHandle,
                out FileLength64,
                filename,
                FILE_READ_DATA,         // DesiredAccess
                0,                      // FileAttributes
                FILE_SHARE_READ,        // ShareAccess
                FILE_OPEN);             // CreateDisposition
            if (!create_result) {
                Dbg("Failed to download file '{0}' from debugger.", filename);
                return false;
            }

            if (FileLength64 > Int32.MaxValue) {
                Dbg("Cannot download ridiculously huge file (>2GiB) over kernel debugger.");
                return false;
            }
            int FileLength = (int)FileLength64;

            try {
                byte[] contents = new byte[FileLength];

                int total_bytes_transferred = 0;

                for (;;) {

                    int bytes_remaining = FileLength - total_bytes_transferred;

                    if (bytes_remaining == 0) {
                        Dbg("Received entire file successfully!");
                        FileData = contents;
                        return true;
                    }

                    int bytes_requested = Math.Min(0x800, bytes_remaining);
                    int bytes_transferred;
                    bool read_result;

                    fixed (byte* contents_pinned = &contents[0])
                    {
                        read_result = ReadHostFile(
                            FileHandle,
                            total_bytes_transferred,
                            &contents_pinned[total_bytes_transferred],
                            bytes_requested,
                            out bytes_transferred);
                    }

                    if (!read_result) {
                        Dbg("FAILED to receive part of file.  Read at offset 0x{0:x} failed.", total_bytes_transferred);
                        FileData = null;
                        return false;
                    }

                    if (bytes_transferred == 0) {
                        Dbg("FAILED to receive all bytes of file.  Received {0} of {1} bytes.", total_bytes_transferred, FileLength);
                        FileData = null;
                        return false;
                    }

                    total_bytes_transferred += bytes_transferred;
                }
            }
            finally {
                CloseHostFile(FileHandle);
            }
        }
    }

    #region KD/DbgEng-compatible structures
    // These structures define the format of messages exchanged between the kernel and
    // the kernel debugger (KD/DbgEng).  Explicit layout is used to eliminate any possibility
    // of smart compilers helping out.
    //
    // In KD/NT, there are no request/response structures.  Instead, the same structure is used
    // for each specific request type.  I have split the structures into request/response, and
    // used explicit field offsets to make sure that the fields are in the right places.  Code
    // that builds requests should always use "new XxxRequest()", in order to guarantee that
    // memory locations within the structures that are not covered by fields are zero-filled.

    /// <summary>
    /// Encodes the "Create Host File" request, which allows this OS instance to open a file that
    /// resides on the debugger's machine, with the cooperation of the host debugger.
    /// 
    /// This structure is bit-compatible with the Windows DBGKD_CREATE_FILE structure, defined in ntdbg.h,
    /// at least when that structure is used as a request.
    /// 
    /// The name of the file to open is carried in the "additional data", and is encoded in UTF-16 (LE),
    /// with a Unicode NUL terminator.  The name provided has meaning only to KD; KD uses a look-up table,
    /// whose contents are set up by the .kdfiles debugger command, to translate these filenames into
    /// actual host filenames.
    /// </summary>
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit, Size = 56)]
    struct CreateHostFileRequest
    {
        [FieldOffset(0)] public uint DesiredAccess;
        [FieldOffset(4)] public uint FileAttributes;
        [FieldOffset(8)] public uint ShareAccess;
        [FieldOffset(12)] public uint CreateDisposition;
        [FieldOffset(16)] public uint CreateOptions;
    }
    
    /// <summary>
    /// This structure defines the response to the "Create Host File" request.  This structure is bit-
    /// compatible with the Windows DBGKD_CREATE_FILE structure, at least with the fields relevant when
    /// that structure is used as a response.
    /// 
    /// The field offsets may look strange -- why don't the fields start at 0?  The reason is that
    /// KD uses the same structure for both the request and (matching) response.  So the fields in
    /// this structure were originally part of DBGKD_CREATE_FILE / CreateHostFileRequest.  Even then,
    /// you need to take into account the 8-byte alignment for FileHandle; the compiler inserts 4
    /// byte of padding alignment between CreateOptions and FileHandle.
    /// 
    /// </summary>
    [StructLayout(LayoutKind.Explicit, Size = 56)]
    struct CreateHostFileResponse
    {
        [FieldOffset(24)] public long FileHandle;
        [FieldOffset(32)] public long FileLength;
    }

    /// <summary>
    /// Encodes the "Read Host File" request.  This structure is bit-compatible with the Windows
    /// DBGKD_READ_FILE structure, defined in ntdbg.h, when used as a request.
    /// 
    /// Data is returned as additional data in the response.
    /// 
    /// This structure is used for both the request and response.
    /// </summary>
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit, Size = 56)]
    struct ReadHostFileRequest
    {
        [FieldOffset(0)] public long FileHandle;
        [FieldOffset(8)] public long FileOffset;
        [FieldOffset(16)] public uint Length;
    }

    /// <summary>
    /// Encodes the "Read Host File" response.  This structure is bit-compatible with the Windows
    /// DBGKD_READ_FILE structure, defined in ntdbg.h, when used as a response.
    /// </summary>
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit, Size = 56)]
    struct ReadHostFileResponse
    {
        [FieldOffset(16)] public uint BytesTransferred;
    }

    /// <summary>
    /// Encodes the "Write Host File" request.  This structure is bit-compatible with the Windows
    /// DBGKD_WRITE_FILE structure, if you exclude the header.
    /// 
    /// The data to write is carried in the "additional data" field.
    /// 
    /// This structure is used for both the request and response.
    /// </summary>
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit, Size = 56)]
    struct WriteHostFileRequest
    {
        [FieldOffset(0)] public long FileHandle;
        [FieldOffset(8)] public long FileOffset;
        [FieldOffset(16)] public uint Length;
    }

    /// <summary>
    /// Encodes the "Write Host File" response.  This structure is bit-compatible with the Windows
    /// DBGKD_WRITE_FILE_STRUCTURE, when used as a response.
    /// </summary>
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit, Size = 56)]
    struct WriteHostFileResponse
    {
        [FieldOffset(16)] public uint BytesTransferred;
    }

    /// <summary>
    /// Encodes the "Close Host File" request.  This structure is bit-compatible with the Windows
    /// DBGKD_CLOSE_FILE structure.  There is no matching CloseHostFileResponse structure, because
    /// there are no request-specific return fields.
    /// </summary>
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit, Size = 56)]
    public struct CloseHostFileRequest
    {
        [FieldOffset(0)] public long FileHandle;
    }

    /// <summary>
    /// All reqests transmitted from the kernel to the debugger (KD) use this message format.
    /// The length is always 64 bytes.
    /// 
    /// This structure is bit-compatible with the Windows DBGKD_FILE_IO structure.
    /// </summary>
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit, Size = 64)]
    struct HostFileIoRequest
    {
        [FieldOffset(0)] public uint ApiNumber;
        [FieldOffset(8)] public CreateHostFileRequest CreateFile;
        [FieldOffset(8)] public CloseHostFileRequest CloseFile;
        [FieldOffset(8)] public ReadHostFileRequest ReadFile;
        [FieldOffset(8)] public WriteHostFileRequest WriteFile;
    }

    /// <summary>
    /// All responses transmitted from the debugger (KD) to the kernel use this message format.
    /// The length is always 64 bytes.
    /// 
    /// This structure is bit-compatible with the Windows DBGKD_FILE_IO structure.
    /// </summary>
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit, Size = 64)]
    struct HostFileIoResponse
    {
        [FieldOffset(4)] public uint Status;
        [FieldOffset(8)] public CreateHostFileResponse CreateFile;
        [FieldOffset(8)] public ReadHostFileResponse ReadFile;
        [FieldOffset(8)] public WriteHostFileResponse WriteFile;
    }

    #endregion
}

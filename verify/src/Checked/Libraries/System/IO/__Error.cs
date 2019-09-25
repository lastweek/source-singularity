// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  __Error
//
// Purpose: Centralized error methods for the IO package.
// Mostly useful for translating Win32 HRESULTs into meaningful
// error strings & exceptions.
//
//===========================================================  

using System;
using System.Runtime.InteropServices;
using System.Text;
//using Microsoft.Singularity.Directory;


namespace System.IO
{
    // Only static data no need to serialize
    internal sealed class __Error
    {
        private __Error() {
        }

        internal static void EndOfFile() {
            throw new EndOfStreamException("IO.EOF_ReadBeyondEOF");
        }

        private static String GetMessage(int errorCode) {
            return String.Format("IO_UnknownError {0}", errorCode);
        }

        internal static void FileNotOpen() {
            throw new ObjectDisposedException(null, "ObjectDisposed_FileClosed");
        }

        internal static void StreamIsClosed() {
            throw new ObjectDisposedException(null, "ObjectDisposed_StreamClosed");
        }

        internal static void MemoryStreamNotExpandable() {
            throw new NotSupportedException("NotSupported_MemStreamNotExpandable");
        }

        internal static void ReaderClosed() {
            throw new ObjectDisposedException(null, "ObjectDisposed_ReaderClosed");
        }

        internal static void ReadNotSupported() {
            throw new NotSupportedException("NotSupported_UnreadableStream");
        }

        internal static void SeekNotSupported() {
            throw new NotSupportedException("NotSupported_UnseekableStream");
        }

        internal static void WrongAsyncResult() {
            throw new ArgumentException("Arg_WrongAsyncResult");
        }

        internal static void EndReadCalledTwice() {
            throw new InvalidOperationException("InvalidOperation_EndReadCalledMultiple");
        }

        internal static void EndWriteCalledTwice() {
            throw new InvalidOperationException("InvalidOperation_EndWriteCalledMultiple");
        }

/*
        internal static void WinIOError() {
            WinIOError(0, String.Empty);
        }

        internal static void SingularityIOError(ErrorCode code, String str) {
            string errString = SdsUtils.ErrorCodeToString(code);
            switch (code) {
                 case ErrorCode.NotFound :{
                    throw new FileNotFoundException(String.Format("FileNotFound: {0}", str));
                }
                default: {
                    throw new IOException(String.Format("{0}: {1}", errString, str));
                }
            }
        }

        internal  static int ErrorCodeToWin32Error(ErrorCode  code)
        {
            // Console.WriteLine("Converting error {0}", SdsUtils.ErrorCodeToString(code));
            int win32 = 0; 
            switch (code) {
                case ErrorCode.NoError :
                    win32 = 0; 
                    break;
                case ErrorCode.AccessDenied :
                    win32 = ERROR_ACCESS_DENIED; 
                    break;
                case ErrorCode.AlreadyExists :
                    win32 = ERROR_FILE_EXISTS; 
                    break;
                case ErrorCode.BadArguments:
                    win32 = ERROR_INVALID_PARAMETER; 
                    break;
                case ErrorCode.ContractNotSupported :
                    win32 = ERROR_INVALID_PARAMETER; 
                    break;
                case ErrorCode.NotFound :
                    win32 = ERROR_FILE_NOT_FOUND; 
                    break;
                case ErrorCode.NotSupported :
                    win32 = ERROR_INVALID_PARAMETER; 
                    break;
                default :
                    win32 = ERROR_INVALID_PARAMETER; 
                    break;
            }
            return win32; 
        }

        // After calling GetLastWin32Error(), it clears the last error field,
        // so you must save the HResult and pass it to this method.  This method
        // will determine the appropriate exception to throw dependent on your
        // error, and depending on the error, insert a string into the message
        // gotten from the ResourceManager.
        internal static void WinIOError(int errorCode, String str) {
            switch (errorCode) {
              case ERROR_FILE_NOT_FOUND: {
                  throw new FileNotFoundException("FileNotFound:" + str);
              }
              case ERROR_PATH_NOT_FOUND: {
                  throw new DirectoryNotFoundException("PathNotFound");
              }
              case ERROR_FILENAME_EXCED_RANGE: {
                  throw new PathTooLongException("PathTooLong");
              }
              case ERROR_INVALID_PARAMETER: {
                  throw new IOException("Invalid Parameter");
              }
              case ERROR_SHARING_VIOLATION: {
                  throw new IOException("SharingViolation");
              }
              case ERROR_FILE_EXISTS: {
                  throw new IOException("FileExists");
              }
              default: {
                  throw new IOException("Unexpanded error code");
              }
            }
        }
*/

        internal static void WriteNotSupported() {
            throw new NotSupportedException("NotSupported_UnwritableStream");
        }

        internal static void WriterClosed() {
            throw new ObjectDisposedException(null, "ObjectDisposed_WriterClosed");
        }

        private const int FORMAT_MESSAGE_IGNORE_INSERTS = 0x00000200;
        private const int FORMAT_MESSAGE_FROM_SYSTEM    = 0x00001000;
        private const int FORMAT_MESSAGE_ARGUMENT_ARRAY = 0x00002000;

/*
        // From WinError.h
        public  const int ERROR_FILE_NOT_FOUND = Native.ERROR_FILE_NOT_FOUND;
        public const int ERROR_PATH_NOT_FOUND = Native.ERROR_PATH_NOT_FOUND;
        public const int ERROR_ACCESS_DENIED  = Native.ERROR_ACCESS_DENIED;
        public const int ERROR_INVALID_PARAMETER = Native.ERROR_INVALID_PARAMETER;
        public const int ERROR_FILENAME_EXCED_RANGE = 0xCE;
        public const int ERROR_SHARING_VIOLATION = 0x20;
        public const int ERROR_FILE_EXISTS = 0x50;

        public const int ERROR_NOT_SUPPORTED = Native.ERROR_NOT_SUPPORTED; 
        public const int ERROR_DUP_NAME = Native.ERROR_DUP_NAME; 
        public const int ERROR_DISK_FULL = Native.ERROR_DISK_FULL; 
        public const int ERROR_CALL_NOT_IMPLEMENTED = Native.ERROR_CALL_NOT_IMPLEMENTED; 
        public const int ERROR_DIR_NOT_EMPTY = Native.ERROR_DIR_NOT_EMPTY; 
        public const int ERROR_ALREADY_EXISTS = Native.ERROR_ALREADY_EXISTS; 
*/

    }
}

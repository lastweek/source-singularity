//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//
/*

using System;
using System.Text;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;
using Microsoft.SingSharp;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using FileSystem.Utils;
using Microsoft.Singularity.V1.Services;

namespace System
{
    [CLSCompliant(false)]
    internal sealed class Native
    {
    
        internal static int GetFileType(IntPtr handle)
        {
            throw new NotSupportedException();
        }

        // Note, these are const used to extract handles, and are NOT handles.
        internal const int STD_INPUT_HANDLE = -10;
        internal const int STD_OUTPUT_HANDLE = -11;
        internal const int STD_ERROR_HANDLE = -12;

        // From WinBase.h
        internal const int FILE_TYPE_DISK = 0x0001;
        internal const int FILE_TYPE_CHAR = 0x0002;
        internal const int FILE_TYPE_PIPE = 0x0003;

        // Error codes from WinError.h
        internal const int ERROR_FILE_NOT_FOUND = 0x2;
        internal const int ERROR_PATH_NOT_FOUND = 0x3;
        internal const int ERROR_ACCESS_DENIED  = 0x5;
        internal const int ERROR_INVALID_HANDLE = 0x6;
        internal const int ERROR_NO_MORE_FILES = 0x12;
        internal const int ERROR_NOT_READY = 0x15;
        internal const int ERROR_SHARING_VIOLATION = 0x20;
        internal const int ERROR_FILE_EXISTS = 0x50;
        internal const int ERROR_INVALID_PARAMETER = 0x57;
        internal const int ERROR_CALL_NOT_IMPLEMENTED = 0x78;
        internal const int ERROR_PATH_EXISTS = 0xB7;
        internal const int ERROR_FILENAME_EXCED_RANGE = 0xCE;  // filename too long.
        internal const int ERROR_DLL_INIT_FAILED = 0x45A;
        
        internal const int ERROR_NOT_SUPPORTED = 50; 
        internal const int ERROR_DUP_NAME = 52; 
        internal const int ERROR_DISK_FULL = 112; 
        internal const int ERROR_DIR_NOT_EMPTY = 145; 
        internal const int ERROR_ALREADY_EXISTS = 183; 

        //////////////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////////////

        internal struct FILE_ATTRIBUTE_DATA {
            internal int fileAttributes;
            internal long ftCreationTime;
            internal long ftLastAccessTime;
            internal long ftLastWriteTime;
            internal long fileSize;
        }

        private static TRef<DirectoryServiceContract.Imp:Ready>       m_epDS= null;

        private static DirectoryServiceContract.Imp:Ready! GetDirectoryServiceContract() 
        {
            if (m_epDS == null) {
                m_epDS = new TRef<DirectoryServiceContract.Imp:Ready>(DirectoryService.NewClientEndpoint());
            }

            return m_epDS.Acquire();
       }

        private static void ReleaseDirectoryServiceContract([Claims] DirectoryServiceContract.Imp:Ready! imp) 
        {
            m_epDS.Release(imp);
        }

        // From WinBase.h
        internal static int ExpandEnvironmentStrings(String lpSrc, StringBuilder lpDst, int nSize)
        {
            throw new NotSupportedException();
        }

        // Called by System.Runtime.InteropServices.Marshal.AllocHGlobal
        // for creation of delegates.
        internal static IntPtr LocalAlloc(int sizetdwBytes)
        {
            throw new NotSupportedException();
        }

        // Called by System.Runtime.InteropServices.Marshal.FreeHGlobal
        // for destruction of delegates.
        internal static IntPtr LocalFree(IntPtr handle)
        {
            throw new NotSupportedException();
        }

        internal static uint GetTempPath(int bufferLen, StringBuilder buffer)
        {
            throw new NotSupportedException();
        }

        // For GetFullPathName, the last param is a useless TCHAR**, set by native.
        internal static int GetFullPathName(String path, int numBufferChars, StringBuilder! buffer)
        {
#if false // uncomment to debug file access.
            Console.WriteLine("GetFullPathName({0})", path);
#endif
            buffer.Append(path);
            return buffer.Length;
        }

        internal static int SearchPath(String path, String fileName, String extension, int numBufferChars, StringBuilder buffer, int[] filePart)
        {
            throw new NotSupportedException();
        }

        // Do not use these directly, use the safe or unsafe versions above.
        // The safe version does not support devices (aka if will only open
        // files on disk), while the unsafe version give you the full semantic
        // of the native version.

        internal static IntPtr CreateFile(String lpFileName,
                                          int dwDesiredAccess,
                                          int dwShareMode,
                                          int dwCreationDisposition,
                                          int dwFlagsAndAttributes)
        {
            throw new NotSupportedException();
        }

        internal static bool CloseHandle(IntPtr handle)
        {
            throw new NotSupportedException();
        }

        internal static bool SetEndOfFile(IntPtr hFile)
        {
            throw new NotSupportedException();
        }

        internal static long SetFilePointer(IntPtr handle, long offset, System.IO.SeekOrigin origin)
        {
            return 0;
        }

        internal static int GetSystemDirectory(StringBuilder sb, int length)
        {
            throw new NotSupportedException();
        }

        internal static bool GetFileTime(IntPtr hFile, long[] creationTime,
                                                long[] lastAccessTime, long[] lastWriteTime)
        {
            throw new NotSupportedException();
        }

        internal static bool SetFileTime(IntPtr hFile, long[] creationTime,
                                                long[] lastAccessTime, long[] lastWriteTime)
        {
            throw new NotSupportedException();
        }

        internal static long GetFileSize(IntPtr hFile)
        {
            throw new NotSupportedException();
        }

        internal static bool LockFile(IntPtr handle, long offset, long count)
        {
            throw new NotSupportedException();
        }

        internal static bool UnlockFile(IntPtr handle,long offset,long count)
        {
            throw new NotSupportedException();
        }

        // Constants from WinNT.h
        internal const int FILE_ATTRIBUTE_DIRECTORY = 0x10;

        // Win32 Structs in N/Direct style
        internal class FIND_DATA {
            internal int  dwFileAttributes = 0;
            // ftCreationTime was a by-value FILETIME structure
            internal long ftCreationTime = 0 ;
            // ftLastAccessTime was a by-value FILETIME structure
            internal long ftLastAccessTime = 0;
            // ftLastWriteTime was a by-value FILETIME structure
            internal long  ftLastWriteTime = 0;
            internal long  nFileSize = 0;
            internal String   cFileName = null;
            internal String   cAlternateFileName = null;
        }

        internal static bool CopyFile(String src, String dst, bool failIfExists) {
            // Modifications to try to make this work on Singularity
            
            // FOR DEBUG
            // Console.WriteLine("Entering Native.CopyFile");
            // Console.WriteLine("src = {0}, dst = {1}, failIfExists = {2}", src, dst, failIfExists);
            // END DEBUG
            ErrorCode error = ErrorCode.Unknown;            

            if (src == null) {
                return false;
            }
            if (dst == null) {
                return false;
            }
            DirectoryServiceContract.Imp ds = GetDirectoryServiceContract();
            if (ds == null) {
                throw new Exception("Unable to acquire handle to the directory");
            }
            
            if (failIfExists) {
                // FOR DEBUG
                // Console.WriteLine("Native.CopyFile: before existence check on dst");
                // END DEBUG
                bool good = FileUtils.FileExists(ds, dst);
                if (!good) {
                    // FOR DEBUG
                    // Console.WriteLine("File copy failed - destination exists and overwrite not set");
                    // END DEBUG
                    ReleaseDirectoryServiceContract(ds);
                    return good;
                }
            }
            // FOR DEBUG
            // Console.WriteLine("Native.CopyFile: before copy");
            // END DEBUG
            bool ok = CopyFile(src, dst, ds, out error);
            ReleaseDirectoryServiceContract(ds);
            return ok;

        } // end CopyFile(String src, String dst, bool failIfExists)

        // true is success
        internal static bool CopyFile(String! srcpath, String! destpath, DirectoryServiceContract.Imp:Ready! ds, out ErrorCode error) {
            int readSize = 4096;
            long readOffset = 0;
            long bytesRead;
            long bytesWrite;
            byte [] bytes = new byte[readSize];

            error = ErrorCode.Unknown;

            if (!FileUtils.CreateFile(destpath, ds, out error)) {
                // FOR DEBUG
                // Console.WriteLine("Native.CopyFile: destination file creation failed");
                // END DEBUG
                return false;
            }

            FileContract.Imp:Ready fileImp = FileUtils.OpenFile(srcpath, ds);
            if (fileImp == null) {
                delete fileImp;
                error = ErrorCode.NotFound;
                // FOR DEBUG
                // Console.WriteLine("Native.CopyFile: unable to open file " + srcpath);
                // END DEBUG
                return false;
            }

            FileContract.Imp:Ready fileOut = FileUtils.OpenFile(destpath, ds, out error);
            if (fileOut == null) {
                delete fileOut;
                // FOR DEBUG
                //Console.WriteLine("Native.CopyFile: unable to open file " + destpath + ". Reason=" + SdsUtils.ErrorCodeToString(error));
                // END DEBUG
                delete fileImp;
                return false;
            }

            do
            {
                bytesRead = FileUtils.Read(fileImp, 0, readSize, readOffset, bytes);
                bytesWrite = FileUtils.Write(fileOut, 0, (int)bytesRead, readOffset, bytes);
                if (bytesRead < readSize) { // error or done with the file
                    break;
                }
                if (bytesWrite < bytesRead) { // error on write
                    // FOR DEBUG
                    // Console.WriteLine("Native.CopyFile: error writing " + destpath);
                    // END DEBUG
                    delete fileImp;
                    delete fileOut;
                    error = ErrorCode.Unknown;
                    return false;
                    break;
                }
                readOffset += bytesRead; // if we got to this point, increment the offset...
            } while (true);
            delete fileImp;
            delete fileOut;
            return true;

        } // end CopyFile (src, dst, ds, out error)

        internal static bool CreateDirectory(
            String path, int lpSecurityAttributes)
        {
            throw new NotSupportedException();
        }

#if false
    internal static bool DeleteFile(String path) 
    {
        ErrorCode error;
        if (path == null) {
            return false;
        }
        DirectoryServiceContract.Imp ds = GetDirectoryServiceContract();
        bool ok = DeleteFile(path, ds, out error); 
        ReleaseDirectoryServiceContract(ds);
        return ok;  
    }
#endif        
    
    internal static bool DeleteFile(String path, out ErrorCode error) {
        error = ErrorCode.Unknown;
        if (path == null) {
            return false;
        }
        DirectoryServiceContract.Imp ds = GetDirectoryServiceContract();
        bool ok = DeleteFile(path, ds, out error); 
        ReleaseDirectoryServiceContract(ds);
        return ok;  
        }

        internal static bool DeleteFile(String! path, DirectoryServiceContract.Imp:Ready! ds, out ErrorCode error) 
        {
            FileUtils.DeleteFile(path, ds, out error);
            bool ok = (error == ErrorCode.NoError);
            if (!ok) {
                DebugStub.WriteLine(" File ({0}) delete failed. reason:{1}",
                  __arglist(path, SdsUtils.ErrorCodeToString(error)) ); 
            } 
            return ok; 
        }

        internal static bool FindClose(IntPtr hndFindFile)
        {
            throw new NotSupportedException();
        }

        internal static IntPtr FindFirstFile(String pFileName,
                                             out FIND_DATA pFindFileData)
        {
            pFindFileData = null;
            throw new NotSupportedException();
        }

        internal static bool FindNextFile(IntPtr hndFindFile,
                                                 out FIND_DATA lpFindFileData)
        {
            lpFindFileData = null;
            throw new NotSupportedException();
        }

        internal static int GetCurrentDirectory(
            int nBufferLength,
            StringBuilder lpBuffer)
        {
            throw new NotSupportedException();
        }

        internal static bool GetFileAttributesEx(String name,
                                                        int fileInfoLevel,
                                                        ref FILE_ATTRIBUTE_DATA lpFileInformation)
        {
            FileAttributesRecord fileAttributes;    
            ErrorCode error;

            if (name == null) return false;
            
            DirectoryServiceContract.Imp ds = GetDirectoryServiceContract();
            if (ds == null) {
                throw new Exception("Unable to acquire handle to the directory");
            }
            
            // get extended file info 
            bool ok = FileUtils.GetAttributes(name, ds, 
                out fileAttributes, out error);
            ReleaseDirectoryServiceContract(ds);

            if (ok) {
                lpFileInformation.ftCreationTime = 
                    fileAttributes.CreationTime;
                lpFileInformation.ftLastAccessTime =
                    fileAttributes.LastAccessTime;
                lpFileInformation.ftLastWriteTime =
                    fileAttributes.LastWriteTime;
                lpFileInformation.fileSize =
                    fileAttributes.FileSize;
            }        
            return ok;
        }

        internal static bool SetFileAttributes(String name, int attr)
        {
            throw new NotSupportedException();
        }

        internal static int GetLogicalDrives()
        {
            throw new NotSupportedException();
        }

        internal static uint GetTempFileName(String tmpPath, String prefix, uint uniqueIdOrZero, StringBuilder tmpFileName)
        {
            throw new NotSupportedException();
        }

        internal static bool MoveFile(String src, String dst)
        {
            throw new NotSupportedException();
        }

        internal static bool RemoveDirectory(String path, out ErrorCode error)
        {
            throw new NotSupportedException();
        }

        internal static bool SetCurrentDirectory(String path)
        {
            throw new NotSupportedException();
        }

        internal const int SHGFP_TYPE_CURRENT               = 0;             // the current (user) folder path setting
        internal const int UOI_FLAGS                        = 1;
        internal const int WSF_VISIBLE                      = 1;
        internal const int CSIDL_APPDATA                    = 0x001a;
        internal const int CSIDL_COMMON_APPDATA             = 0x0023;
        internal const int CSIDL_LOCAL_APPDATA              = 0x001c;
        internal const int CSIDL_COOKIES                    = 0x0021;
        internal const int CSIDL_FAVORITES                  = 0x0006;
        internal const int CSIDL_HISTORY                    = 0x0022;
        internal const int CSIDL_INTERNET_CACHE             = 0x0020;
        internal const int CSIDL_PROGRAMS                   = 0x0002;
        internal const int CSIDL_RECENT                     = 0x0008;
        internal const int CSIDL_SENDTO                     = 0x0009;
        internal const int CSIDL_STARTMENU                  = 0x000b;
        internal const int CSIDL_STARTUP                    = 0x0007;
        internal const int CSIDL_SYSTEM                     = 0x0025;
        internal const int CSIDL_TEMPLATES                  = 0x0015;
        internal const int CSIDL_DESKTOPDIRECTORY           = 0x0010;
        internal const int CSIDL_PERSONAL                   = 0x0005;
        internal const int CSIDL_PROGRAM_FILES              = 0x0026;
        internal const int CSIDL_PROGRAM_FILES_COMMON       = 0x002b;
        internal const int CSIDL_DESKTOP                    = 0x0000;
        internal const int CSIDL_DRIVES                     = 0x0011;
        internal const int CSIDL_MYMUSIC                    = 0x000d;
        internal const int CSIDL_MYPICTURES                 = 0x0027;


        internal static int GetModuleFileName(IntPtr hModule, StringBuilder buffer, int length)
        {
            throw new NotSupportedException();
        }

        internal static bool GetUserName(StringBuilder lpBuffer, int[] nSize)
        {
            throw new NotSupportedException();
        }

        internal static int SHGetFolderPath(IntPtr hwndOwner, int nFolder, IntPtr hToken, int dwFlags, StringBuilder lpszPath)
        {
            throw new NotSupportedException();
        }

        internal static bool LookupAccountName(string machineName, string accountName, byte[] sid,
                                               ref int sidLen, StringBuilder domainName, ref int domainNameLen, out int peUse)
        {
            peUse = 0;
            throw new NotSupportedException();
        }
    }
}
*/

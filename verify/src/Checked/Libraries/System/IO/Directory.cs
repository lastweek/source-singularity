// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Directory
//
// Purpose: Exposes routines for enumerating through a
// directory.
//
//===========================================================  

using System;
using System.Collections;
using Microsoft.Singularity;
using System.Text;
using System.Runtime.InteropServices;
using System.Globalization;
//using Microsoft.Singularity.Directory;
//using FileSystem.Utils;

namespace System.IO
{
/*
    //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory"]/*' />
    public sealed class Directory {
        private Directory()
        {
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetParent"]/*' />
        public static DirectoryInfo GetParent(String path)
        {
            if (path == null)
                throw new ArgumentNullException("path");

            if (path.Length == 0)
                throw new ArgumentException("Argument_PathEmpty", "path");

            String fullPath = Path.GetFullPathInternal(path);

            String s = Path.GetDirectoryName(fullPath);
            if (s == null)
                 return null;
            return new DirectoryInfo(s);
        }


        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.CreateDirectory"]/*' />
        public static DirectoryInfo CreateDirectory(String path) {
            if (path == null)
                throw new ArgumentNullException("path");
            if (path.Length == 0)
                throw new ArgumentException("Argument_PathEmpty");

            String fullPath = Path.GetFullPathInternal(path);

            // You need read access to the directory to be returned back and write access to all the directories
            // that you need to create. If we fail any security checks we will not create any directories at all.
            // We attempt to create directories only after all the security checks have passed. This is avoid doing
            // a demand at every level.
            InternalCreateDirectory(fullPath,path);

            return new DirectoryInfo(fullPath, false);
        }

        internal static void InternalCreateDirectory(String! fullPath, String path) {
            int length = fullPath.Length;

            // We need to trim the trailing slash or the code will try to create 2 directories of the same name.
            if (length >= 2 && Path.IsDirectorySeparator(fullPath[length - 1]))
                length--;
            int i = Path.GetRootLength(fullPath);

            // For UNC paths that are only // or ///
            if (length == 2 && Path.IsDirectorySeparator(fullPath[1]))
                throw new IOException(String.Format("IO.IO_CannotCreateDirectory",path));

            ArrayList list = new ArrayList();

            while (i < length) {
                i++;
                while (i < length && fullPath[i] != Path.DirectorySeparatorChar && fullPath[i] != Path.AltDirectorySeparatorChar) i++;
                String dir = fullPath.Substring(0, i);

                if (!InternalExists(dir)) { // Create only the ones missing
                    list.Add(dir);
                }
            }

            if (list.Count != 0) {
                String [] securityList = (String[])list.ToArray(typeof(String));
                for (int j = 0; j < securityList.Length; j++)
                    securityList[j] += "\\."; // leafs will never has a slash at the end
            }


            // We need this check to mask OS differences
            // Handle CreateDirectory("X:\\") when X: doesn't exist. Similarly for n/w paths.
            String root = InternalGetDirectoryRoot(fullPath);
            if (!InternalExists(root)) {
                // Extract the root from the passed in path again for security.
                __Error.WinIOError(Native.ERROR_PATH_NOT_FOUND, InternalGetDirectoryRoot(path));
            }

            bool r = true;
            int firstError = 0;
            // If all the security checks succeeded create all the directories
            for (int j = 0; j < list.Count; j++) {
                String name = (String!)list[j];
                if (name.Length > Path.MAX_DIRECTORY_PATH)
                    throw new PathTooLongException("IO.PathTooLong");
                r = Native.CreateDirectory(name, 0);
                if (!r && (firstError == 0)) {
                    firstError = Native.ERROR_PATH_EXISTS;
                }
            }

            if (!r && (firstError != 0)) {
                __Error.WinIOError(firstError, path);
            }
        }


        // Tests if the given path refers to an existing DirectoryInfo on disk.
        //
        // Your application must have Read permission to the directory's
        // contents.
        //
        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.Exists"]/*' />

        public static bool Exists(String! path) 
        {
            try {
                path = Path.GetFullPathInternal(path);
                
                if (path == null) return false;
                if (path.Length == 0) return false;
                    
                bool isDir;    
                int ok = DirectoryUtils.PathIsDirectory(path, out isDir);
                if (ok != 0) return false;
                return isDir; 
            }
            catch (ArgumentException) {

            }
            catch (NotSupportedException) {

            }
            return false;
        }      
                 
        // Determine whether path describes an existing directory
        // on disk, avoiding security checks.
        internal static bool InternalExists(String path) 
        {
            Native.FILE_ATTRIBUTE_DATA data = new Native.FILE_ATTRIBUTE_DATA();
            int dataInitialised = File.FillAttributeInfo(path,ref data);
            if (dataInitialised != 0)
                return false;

            return data.fileAttributes != -1 && (data.fileAttributes & Native.FILE_ATTRIBUTE_DIRECTORY) != 0;
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.SetCreationTime"]/*' />
        public static void SetCreationTime(String! path, DateTime creationTime)
        {
            SetCreationTimeUtc(path, creationTime.ToUniversalTime());
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.SetCreationTimeUtc"]/*' />
        public static void SetCreationTimeUtc(String! path, DateTime creationTimeUtc)
        {
            IntPtr handle = Directory.OpenHandle(path);
            bool r = Native.SetFileTime(handle,  new long[] {creationTimeUtc.ToFileTimeUtc()}, null, null);
            if (!r) {
                Native.CloseHandle(handle);
                __Error.WinIOError(1, path);
            }
            Native.CloseHandle(handle);
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetCreationTimeUtc"]/*' />
        public static DateTime GetCreationTimeUtc(String! path)
        {
            return File.GetCreationTimeUtc(path);
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.SetLastWriteTimeUtc"]/*' />
        public static void SetLastWriteTimeUtc(String! path, DateTime lastWriteTimeUtc)
        {
            IntPtr handle = Directory.OpenHandle(path);
            bool r = Native.SetFileTime(handle,  null, null, new long[] {lastWriteTimeUtc.ToFileTimeUtc()});
            if (!r) {
                Native.CloseHandle(handle);
                __Error.WinIOError(1, path);
            }
            Native.CloseHandle(handle);
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetLastWriteTimeUtc"]/*' />
        public static DateTime GetLastWriteTimeUtc(String! path)
        {
            return File.GetLastWriteTimeUtc(path);
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.SetLastAccessTimeUtc"]/*' />
        public static void SetLastAccessTimeUtc(String! path, DateTime lastAccessTimeUtc)
        {
            IntPtr handle = Directory.OpenHandle(path);
            bool r = Native.SetFileTime(handle,  null, new long[] {lastAccessTimeUtc.ToFileTimeUtc()}, null);
            if (!r) {
                Native.CloseHandle(handle);
                __Error.WinIOError(1, path);
            }
            Native.CloseHandle(handle);
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetLastAccessTimeUtc"]/*' />
        public static DateTime GetLastAccessTimeUtc(String! path)
        {
            return File.GetLastAccessTimeUtc(path);
        }


       // Returns an array of Files in the DirectoryInfo specified by path
        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetFiles"]/*' />
        public static String[] GetFiles(String path)
        {
            return GetFiles(path,"*");
        }

        // Returns an array of Files in the current DirectoryInfo matching the
        // given search criteria (ie, "*.txt").
        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetFiles1"]/*' />
        public static String[] GetFiles(String path,String searchPattern)
        {
            if (path == null)
                throw new ArgumentNullException("path");

            if (searchPattern == null)
                throw new ArgumentNullException("searchPattern");

            searchPattern = searchPattern.TrimEnd();
            if (searchPattern.Length == 0)
                return new String[0];

            // Must fully qualify the path for the security check
            String fullPath = Path.GetFullPathInternal(path);

            String searchPath = Path.GetDirectoryName(searchPattern);
            if (searchPath != null && searchPath != String.Empty) // For filters like foo\*.cs we need to verify if the directory foo is not denied access.
            {
                path = Path.Combine(path,searchPath); // Need to add the searchPath to return correct path and for right security checks
            }

            // Note - fileNames returned by InternalGetFiles are not fully qualified.
            String [] fileNames = InternalGetFiles(fullPath, path, searchPattern);
            for (int i = 0; i < fileNames.Length; i++)
                fileNames[i] = Path.InternalCombine(path, fileNames[i]);
            return fileNames;
        }

        // Internal helper function with no security checks
        // Note - fileNames returned by InternalGetFiles are not fully qualified.
        // Path should be fully qualified.  userPath is used in exceptions.
        internal static String[]! InternalGetFiles(String path, String userPath, String searchPattern)
        {
            String fullPath = Path.InternalCombine(path, searchPattern);
            String[] fileNames = InternalGetFileDirectoryNames(fullPath, userPath, true);
            return fileNames;
        }

        // Returns an array of Directories in the current directory.
        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetDirectories"]/*' />
        public static String[] GetDirectories(String path)
        {
            return GetDirectories(path,"*");
        }

        // Returns an array of Directories in the current DirectoryInfo matching the
        // given search criteria (ie, "*.txt").
        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetDirectories1"]/*' />
        public static String[] GetDirectories(String path,String searchPattern)
        {
            if (path == null)
                throw new ArgumentNullException("path");

            if (searchPattern == null)
                throw new ArgumentNullException("searchPattern");

            searchPattern = searchPattern.TrimEnd();
            if (searchPattern.Length == 0)
                return new String[0];

            // Must fully qualify the path for the security check
            String fullPath = Path.GetFullPathInternal(path);

            String searchPath = Path.GetDirectoryName(searchPattern);
            if (searchPath != null && searchPath != String.Empty) // For filters like foo\*.cs we need to verify if the directory foo is not denied access.
            {
                path = Path.Combine(path,searchPath); // Need to add the searchPath to return correct path and for right security checks
            }

            String [] dirNames = InternalGetDirectories(fullPath, path, searchPattern);
            for (int i = 0; i < dirNames.Length; i++)
                dirNames[i] = Path.InternalCombine(path, dirNames[i]);
            return dirNames;
        }

        // Internal helper function that has no security checks
        // Note - InternalGetDirectories returns non-qualified directory names.
        // Path should be fully qualified.  userPath is used in exceptions.
        internal static String[]! InternalGetDirectories(String path, String userPath, String searchPattern)
        {
            String fullPath = Path.InternalCombine(path, searchPattern);
            String[] dirNames = InternalGetFileDirectoryNames(fullPath, userPath, false);
            return dirNames;
        }


        // Returns an array of strongly typed FileSystemInfo entries in the path
        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetFileSystemEntries"]/*' />
        public static String[] GetFileSystemEntries(String path)
        {
            return GetFileSystemEntries(path,"*");
        }


        // Returns an array of strongly typed FileSystemInfo entries in the path with the
        // given search criteria (ie, "*.txt"). We disallow .. as a part of the search criteria
        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetFileSystemEntries1"]/*' />
        public static String[] GetFileSystemEntries(String path,String searchPattern)
        {
            if (path == null)
                throw new ArgumentNullException("path");

            if (searchPattern == null)
                throw new ArgumentNullException("searchPattern");

            searchPattern = searchPattern.TrimEnd();
            if (searchPattern.Length == 0)
                return new String[0];

            // Must fully qualify the path for the security check
            String fullPath = Path.GetFullPathInternal(path);
            String searchPath = Path.GetDirectoryName(searchPattern);
            if (searchPath != null && searchPath != String.Empty) // For filters like foo\*.cs we need to verify if the directory foo is not denied access.
            {
               path = Path.Combine(path,searchPath); // Need to add the searchPath to return correct path and for right security checks
            }

            String [] dirs = InternalGetDirectories(fullPath, path, searchPattern);
            String [] files = InternalGetFiles(fullPath, path, searchPattern);
            String [] fileSystemEntries = new String[dirs.Length + files.Length];

            int count = 0;
            for (int i = 0; i < dirs.Length; i++)
                fileSystemEntries[count++] = Path.InternalCombine(path, dirs[i]);

            for (int i = 0; i < files.Length; i++)
                fileSystemEntries[count++] = Path.InternalCombine(path, files[i]);

            return fileSystemEntries;
        }

        // Private helper function that does not do any security checks
        internal static String[]! InternalGetFileDirectoryNames(String! fullPath, String userPath, bool file)
        {
            // If path ends in a trailing slash (\), append a * or we'll
            // get a "Cannot find the file specified" exception
            char lastChar = fullPath[fullPath.Length-1];
            if (lastChar == Path.DirectorySeparatorChar || lastChar == Path.AltDirectorySeparatorChar || lastChar == Path.VolumeSeparatorChar)
                fullPath = fullPath + '*';

            String[] list = new String[10];
            int listSize = 0;
            Native.FIND_DATA data = new Native.FIND_DATA();

            // Open a Find handle (Win32 is weird)
            IntPtr hnd = Native.FindFirstFile(fullPath, out data);
            if (hnd == IntPtr.Zero) {
                return new String[0];
            }

            // Keep asking for more matching files, adding file names to list
            int numEntries = 0;  // Number of DirectoryInfo entities we see.
            do {
                assert data != null; // implied by result of FindFirst/Next not being Zero
                bool includeThis;  // Should this file/DirectoryInfo be included in the output?
                if (file)
                    includeThis = (0==(data.dwFileAttributes & Native.FILE_ATTRIBUTE_DIRECTORY));
                else {
                    includeThis = (0!=(data.dwFileAttributes & Native.FILE_ATTRIBUTE_DIRECTORY));
                    // Don't add "." nor ".."
                    if (includeThis && (data.cFileName.Equals(".") || data.cFileName.Equals("..")))
                        includeThis = false;
                }

                if (includeThis) {
                    numEntries++;
                    if (listSize == list.Length) {
                        String[] newList = new String[list.Length*2];
                        Array.Copy(list, 0, newList, 0, listSize);
                        list = newList;
                    }
                    list[listSize++] = data.cFileName;
                }

            } while (Native.FindNextFile(hnd, out data));

            // Make sure we quit with a sensible error.
            Native.FindClose(hnd);  // Close Find handle in all cases.

            // Check for a string such as "C:\tmp", in which case we return
            // just the DirectoryInfo name.  FindNextFile fails first time, and
            // data still contains a directory.

            // The above comment seems wrong. I don't see why data should still be
            // non-null here.
            assert data != null;

            if (!file && numEntries == 1 && (0!=(data.dwFileAttributes & Native.FILE_ATTRIBUTE_DIRECTORY))) {
                String[] sa = new String[1];
                sa[0] = data.cFileName;
                return sa;
            }

            // Return list of files/directories as an array of strings
            if (listSize == list.Length)
                return list;
            String[] items = new String[listSize];
            Array.Copy(list, 0, items, 0, listSize);
            return items;
        }

        // Retrieves the names of the logical drives on this machine in the
        // form "C:\".
        //
        // Your application must have System Info permission.
        //
        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetLogicalDrives"]/*' />
        public static String[] GetLogicalDrives()
        {
            int drives = Native.GetLogicalDrives();
            if (drives == 0)
                __Error.WinIOError();
            uint d = (uint)drives;
            int count = 0;
            while (d != 0) {
                if (((int)d & 1) != 0) count++;
                d >>= 1;
            }
            String[] result = new String[count];
            char[] root = new char[] {'A', ':', '\\'};
            d = (uint)drives;
            count = 0;
            while (d != 0) {
                if (((int)d & 1) != 0) {
                    result[count++] = new String(root);
                }
                d >>= 1;
                root[0]++;
            }
            return result;
        }


        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetDirectoryRoot"]/*' />
        public static String GetDirectoryRoot(String path) {
            if (path == null)
                throw new ArgumentNullException("path");

            String fullPath = Path.GetFullPathInternal(path);
            return fullPath.Substring(0, Path.GetRootLength(fullPath));
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.InternalGetDirectoryRoot"]/*' />
        internal static String InternalGetDirectoryRoot(String path) {
            if (path == null) return null;
            return path.Substring(0, Path.GetRootLength(path));
        }

        //===============================CurrentDirectory===============================
        //Action:  Provides a getter and setter for the current directory.  The original
        //         current DirectoryInfo is the one from which the process was started.
        //Returns: The current DirectoryInfo (from the getter).  Void from the setter.
        //Arguments: The current DirectoryInfo to which to switch to the setter.
        //Exceptions:
        //==============================================================================  
        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.GetCurrentDirectory"]/*' />
        public static String GetCurrentDirectory()
        {
            StringBuilder sb = new StringBuilder(Path.MAX_PATH + 1);
            if (Native.GetCurrentDirectory(sb.Capacity, sb) == 0)
                System.IO.__Error.WinIOError();
            String currentDirectory = sb.ToString();
            return currentDirectory;
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.SetCurrentDirectory"]/*' />
        public static void SetCurrentDirectory(String path)
        {
            if (path == null)
                throw new ArgumentNullException("value");
            if (path.Length == 0)
                throw new ArgumentException("Argument_PathEmpty");
            if (path.Length >= Path.MAX_PATH)
                throw new PathTooLongException("IO.PathTooLong");

            // This will have some huge effects on the rest of the runtime
            // and every other application.  Make sure app is highly trusted.
            String fulldestDirName = Path.GetFullPathInternal(path);

            // If path doesn't exist, this sets last error to 3 (Path not Found).
            if (!Native.SetCurrentDirectory(fulldestDirName))
                System.IO.__Error.WinIOError(1, path);
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.Move"]/*' />
        public static void Move(String sourceDirName,String destDirName) {
            if (sourceDirName == null)
                throw new ArgumentNullException("sourceDirName");
            if (sourceDirName.Length == 0)
                throw new ArgumentException("Argument_EmptyFileName", "sourceDirName");

            if (destDirName == null)
                throw new ArgumentNullException("destDirName");
            if (destDirName.Length == 0)
                throw new ArgumentException("Argument_EmptyFileName", "destDirName");

            String fullsourceDirName = Path.GetFullPathInternal(sourceDirName);
            String fulldestDirName = Path.GetFullPathInternal(destDirName);

            String sourcePath;
            if (fullsourceDirName.EndsWith('\\'))
                sourcePath = fullsourceDirName;
            else
                sourcePath = fullsourceDirName + "\\";

            String destPath;
            if (fulldestDirName.EndsWith('\\'))
                destPath = fulldestDirName;
            else
                destPath = fulldestDirName + "\\";

            if (CompareInfo.Compare(sourcePath, destPath, CompareOptions.IgnoreCase) == 0)
                throw new IOException("IO.IO_SourceDestMustBeDifferent");

            String sourceRoot = Path.GetPathRoot(sourcePath);
            String destinationRoot = Path.GetPathRoot(destPath);
            if (CompareInfo.Compare(sourceRoot, destinationRoot, CompareOptions.IgnoreCase) != 0)
                throw new IOException("IO.IO_SourceDestMustHaveSameRoot");

            if (!Native.MoveFile(sourceDirName, destDirName)) {
                __Error.WinIOError(1,String.Empty);
            }
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.Delete"]/*' />
        public static void Delete(String! path)
        {
            String fullPath = Path.GetFullPathInternal(path);
            Delete(fullPath, path, false);
        }

        //| <include file='doc\Directory.uex' path='docs/doc[@for="Directory.Delete1"]/*' />
        public static void Delete(String! path, bool recursive)
        {
            String fullPath = Path.GetFullPathInternal(path);
            Delete(fullPath, path, recursive);
        }

        // Called from DirectoryInfo as well.  FullPath is fully qualified,
        // while the user path is used for feedback in exceptions.
        internal static void Delete(String fullPath, String userPath, bool recursive)
        {
            DeleteHelper(fullPath, userPath, recursive);
        }

        // Note that fullPath is fully qualified, while userPath may be
        // relative.  Use userPath for all exception messages to avoid leaking
        // fully qualified path information.
        private static void DeleteHelper(String fullPath, String userPath, bool recursive)
        {
            bool r;
            Exception ex = null;
            ErrorCode error; 
            
            if (recursive) {
                Native.FIND_DATA data = new Native.FIND_DATA();

                // Open a Find handle (Win32 is weird)
                IntPtr hnd = Native.FindFirstFile(fullPath+Path.DirectorySeparatorChar+"*", out data);
                if (hnd == IntPtr.Zero) {
                    __Error.WinIOError(1, userPath);
                }

                do {
                    assert data != null; // implied by FindFirst/NextFile and return status
                    bool isDir = (0!=(data.dwFileAttributes & Native.FILE_ATTRIBUTE_DIRECTORY));
                    if (isDir) {
                        if (data.cFileName.Equals(".") || data.cFileName.Equals(".."))
                            continue;

                        // recurse
                        String newFullPath = Path.InternalCombine(fullPath, data.cFileName);
                        String newUserPath = Path.InternalCombine(userPath, data.cFileName);
                        try {
                            DeleteHelper(newFullPath, newUserPath, recursive);
                        }
                        catch (Exception e) {
                            if (ex == null) {
                                ex = e;
                            }
                        }
                    }
                    else {
                        String fileName = fullPath + Path.DirectorySeparatorChar + data.cFileName;
                        r = Native.DeleteFile(fileName, out error);
                        if (!r) {
                           // __Error.WinIOError(1, data.cFileName);
                            __Error.SingularityIOError(error,data.cFileName); 
                        }
                    }
                } while (Native.FindNextFile(hnd, out data));

                // Make sure we quit with a sensible error.
                Native.FindClose(hnd);  // Close Find handle in all cases.
                if (ex != null)
                    throw ex;
            }

            r = Native.RemoveDirectory(fullPath, out error);
            if (!r)
                //__Error.WinIOError(1, userPath);
                __Error.SingularityIOError(error,fullPath); 
        }


        internal static void VerifyDriveExists(String! root)
        {
            int drives = Native.GetLogicalDrives();
            if (drives == 0)
                __Error.WinIOError();
            uint d = (uint)drives;
            char drive = Char.ToLower(root[0]);
            if ((d & (1 << (drive - 'a'))) == 0)
                throw new DirectoryNotFoundException(String.Format("IO.DriveNotFound_Drive", root));
        }


        private static IntPtr OpenHandle(String! path)
        {
            String fullPath = Path.GetFullPathInternal(path);
            String root = Path.GetPathRoot(fullPath);
            assert root != null;
            if (root == fullPath && root[1] == Path.VolumeSeparatorChar)
                throw new ArgumentException("Arg_PathIsVolume");

            IntPtr handle = Native.CreateFile(
                fullPath,
                GENERIC_WRITE,
                FILE_SHARE_WRITE|FILE_SHARE_DELETE,
                OPEN_EXISTING,
                FILE_FLAG_BACKUP_SEMANTICS
            );

            if (handle == IntPtr.Zero) {
                __Error.WinIOError(1, path);
            }
            return handle;
        }

        private const int FILE_ATTRIBUTE_DIRECTORY = 0x00000010;
        private const int GENERIC_WRITE = unchecked((int)0x40000000);
        private const int FILE_SHARE_WRITE = 0x00000002;
        private const int FILE_SHARE_DELETE = 0x00000004;
        private const int OPEN_EXISTING = 0x00000003;
        private const int FILE_FLAG_BACKUP_SEMANTICS = 0x02000000;
    }
*/
}

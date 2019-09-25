// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  File
//
// Purpose: A collection of methods for manipulating Files.
//
//===========================================================  

using System;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Text;
//using Microsoft.Singularity.Directory;

namespace System.IO
{
    // Class for creating FileStream objects, and some basic file management
    // routines such as Delete, etc.
    //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo"]/*' />
    public sealed class FileInfo//: FileSystemInfo
    {
        private String _name;

        [Microsoft.Contracts.NotDelayed]
        private FileInfo() {
        }

        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.FileInfo"]/*' />
        [Microsoft.Contracts.NotDelayed]
        public FileInfo(String fileName)
        {
/*TODO
            if (fileName == null)
                 throw new ArgumentNullException("fileName");

            OriginalPath = fileName;
            // Must fully qualify the path for the security check
            String fullPath = Path.GetFullPathInternal(fileName);

            _name = Path.GetFileName(fileName);
            FullPath = fullPath;
*/
            _name = fileName;
        }

/*
        [Microsoft.Contracts.NotDelayed]
        internal FileInfo(String! fullPath, bool ignoreThis)
        {
            Debug.Assert(Path.GetRootLength(fullPath) > 0, "fullPath must be fully qualified!");
            _name = Path.GetFileName(fullPath);
            OriginalPath = _name;
            FullPath = fullPath;
        }

            //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.Name"]/*' />
        public override String Name {
            get { return _name; }
        }


        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.Length"]/*' />
        public long Length {
            get {
                if (_dataInitialised == -1)
                    Refresh();

                if (_dataInitialised != 0) // Refresh was unable to initialise the data
                    __Error.WinIOError(_dataInitialised, OriginalPath);

                if ((_data.fileAttributes & Native.FILE_ATTRIBUTE_DIRECTORY) != 0)
                    __Error.WinIOError(Native.ERROR_FILE_NOT_FOUND,OriginalPath);

                return _data.fileSize;
            }
        }

        // Returns the name of the directory that the file is in   
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.DirectoryName"]/*' />
        public String DirectoryName
        {
            get
            {
                String directoryName = Path.GetDirectoryName(FullPath);
                return directoryName;
            }
        }

        // Creates an instance of the the parent directory   
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.Directory"]/*' />
        public DirectoryInfo Directory
        {
            get
            {
                String dirName = DirectoryName;
                if (dirName == null)
                    return null;
                return new DirectoryInfo(dirName);
            }
        }
*/
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.OpenText"]/*' />
        public StreamReader OpenText()
        {
            //return new StreamReader(FullPath, Encoding.UTF8, true, StreamReader.DefaultBufferSize);
            //return new StreamReader(FullPath, Encoding.UTF8, true, StreamReader.DefaultBufferSize);
            return new StreamReader(_name, Encoding.UTF8, true, StreamReader.DefaultBufferSize);
        }

/*
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.CreateText"]/*' />
        public StreamWriter CreateText()
        {
            return new StreamWriter(FullPath,false);
        }


        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.AppendText"]/*' />
        public StreamWriter AppendText()
        {
            return new StreamWriter(FullPath,true);
        }


        // Copies an existing file to a new file. An exception is raised if the
        // destination file already exists. Use the
        // Copy(String, String, boolean) method to allow
        // overwriting an existing file.
        //
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.CopyTo"]/*' />
        public FileInfo CopyTo(String! destFileName) {
            return CopyTo(destFileName, false);
        }

    //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.Create"]/*' />

        public FileStream Create() {
            return File.Create(FullPath);
        }

        // Copies an existing file to a new file. If overwrite is
        // false, then an IOException is thrown if the destination file
        // already exists.  If overwrite is true, the file is
        // overwritten.
        //
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.CopyTo1"]/*' />
        public FileInfo CopyTo(String! destFileName, bool overwrite) {
            destFileName = File.InternalCopy(FullPath, destFileName, overwrite);
            return new FileInfo(destFileName, false);
        }

        // Deletes a file. The file specified by the designated path is deleted.
        // If the file does not exist, Delete succeeds without throwing
        // an exception.
        //
        // On NT, Delete will fail for a file that is open for normal I/O
        // or a file that is memory mapped.  On Win95, the file will be
        // deleted regardless of whether the file is being used.
        //
        // Your application must have Delete permission to the target file.
        //
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.Delete"]/*' />
        public override void Delete() {
            // For security check, path should be resolved to an absolute path.
            ErrorCode error;
            bool r = Native.DeleteFile(FullPath, out error);
            if (!r) {
               // __Error.WinIOError(0, OriginalPath);
                __Error.SingularityIOError(error,OriginalPath); 
            }
        }



        // Tests if the given file exists. The result is true if the file
        // given by the specified path exists; otherwise, the result is
        // false.  Note that if path describes a directory,
        // Exists will return true.
        //
        // Your application must have Read permission for the target directory.
        //
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.Exists"]/*' />
        public override bool Exists {
            get
            {
                try {
                    if (_dataInitialised == -1)
                        Refresh();
                    if (_dataInitialised != 0) // Refresh was unable to initialise the data
                        __Error.WinIOError(_dataInitialised, OriginalPath);

                    return (_data.fileAttributes & Native.FILE_ATTRIBUTE_DIRECTORY) == 0;
                }
                catch (Exception) {
                    return false;
                }
            }
        }




        // User must explicitly specify opening a new file or appending to one.
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.Open"]/*' />
        public FileStream Open(FileMode mode) {
            return Open(mode, FileAccess.ReadWrite, FileShare.None);
        }



        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.Open1"]/*' />
        public FileStream Open(FileMode mode, FileAccess access) {
            return Open(mode, access, FileShare.None);
        }



        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.Open2"]/*' />
        public FileStream Open(FileMode mode, FileAccess access, FileShare share) {
            return new FileStream(FullPath, mode, access, share);
        }




        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.OpenRead"]/*' />
        public FileStream OpenRead() {
            return new FileStream(FullPath, FileMode.Open, FileAccess.Read,
                                  FileShare.Read);
        }



        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.OpenWrite"]/*' />
        public FileStream OpenWrite() {
            return new FileStream(FullPath, FileMode.OpenOrCreate,
                                  FileAccess.Write, FileShare.None);
        }






        // Moves a given file to a new location and potentially a new file name.
        // This method does work across volumes.
        //
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.MoveTo"]/*' />
        public void MoveTo(String destFileName) {
            if (destFileName == null)
                throw new ArgumentNullException("destFileName");
            if (destFileName.Length == 0)
                throw new ArgumentException("Argument_EmptyFileName", "destFileName");

            String fullDestFileName = Path.GetFullPathInternal(destFileName);

            if (!Native.MoveFile(FullPath, fullDestFileName))
                __Error.WinIOError();
            FullPath = fullDestFileName;
            OriginalPath = destFileName;
            _name = Path.GetFileName(fullDestFileName);

            // Flush any cached information about the file.
            _dataInitialised = -1;
        }

#if false
        // Returns the fully qualified path
        //| <include file='doc\FileInfo.uex' path='docs/doc[@for="FileInfo.ToString"]/*' />
        public override String ToString()
        {
            return OriginalPath;
        }
#endif
*/
    }
}

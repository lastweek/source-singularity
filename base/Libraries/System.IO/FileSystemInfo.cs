// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  FileSystemInfo
//
// Purpose:
//
//===========================================================  

using System;
using System.Collections;
using Microsoft.Singularity;
using System.Text;
using System.Runtime.InteropServices;

//@TODO: Add a static SystemDirectory property returning a URI
namespace System.IO
{
    //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo"]/*' />

    public abstract class FileSystemInfo {
        internal Native.FILE_ATTRIBUTE_DATA _data; // Cache the file information
        internal int _dataInitialised = -1; // We use this field in conjunction with the Refresh methods, if we succeed
                                           // we store a zero, on failure we store the HResult in it so that we can
                                           // give back a generic error back.

        private const int ERROR_INVALID_PARAMETER = 87;
        internal const int ERROR_ACCESS_DENIED = 0x5;

        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.FullPath"]/*' />
        protected String FullPath;  // fully qualified path of the directory
        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.OriginalPath"]/*' />
        protected String OriginalPath; // path passed in by the user

        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.FileSystemInfo"]/*' />
        protected FileSystemInfo()
        {
        }

        // Full path of the directory/file
        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.FullName"]/*' />
        public virtual String FullName {
            get
            {
                return FullPath;
            }
        }

        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.Extension"]/*' />
        public String Extension
        {
            get
            {
                // GetFullPathInternal would have already stripped out the terminating "." if present.
               int length = FullPath.Length;
                for (int i = length; --i >= 0;) {
                    char ch = FullPath[i];
                    if (ch == '.')
                        return FullPath.Substring(i, length - i);
                    if (ch == Path.DirectorySeparatorChar || ch == Path.AltDirectorySeparatorChar || ch == Path.VolumeSeparatorChar)
                        break;
                }
                return String.Empty;
            }
        }

        // For files name of the file is returned, for directories the last directory in hierarchy is returned if possible,
        // otherwise the fully qualified name s returned
        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.Name"]/*' />
        public abstract String Name {
            get;
        }

        // Whether a file/directory exists
        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.Exists"]/*' />
        public abstract bool Exists
        {
            get;
        }

        // Delete a file/directory
        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.Delete"]/*' />
        public abstract void Delete();

        public DateTime CreationTime {
            get {
                return CreationTimeUtc.ToLocalTime();
            }

            set {
                CreationTimeUtc = value.ToUniversalTime();
            }
        }

        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.CreationTimeUtc"]/*' />
        public DateTime CreationTimeUtc {
            get {
                if (_dataInitialised == -1) {
                    _data = new Native.FILE_ATTRIBUTE_DATA();
                    Refresh();
                }

                if (_dataInitialised != 0) // Refresh was unable to initialise the data
                    __Error.WinIOError(_dataInitialised, OriginalPath);

                return DateTime.FromFileTimeUtc(_data.ftCreationTime);

            }

            set {
                if (this is DirectoryInfo)
                    Directory.SetCreationTimeUtc(FullPath,value);
                else
                    File.SetCreationTimeUtc(FullPath,value);
                _dataInitialised = -1;
            }
        }

        public DateTime LastAccessTime {
            get {
                return LastAccessTimeUtc.ToLocalTime();
            }

            set {
                LastAccessTimeUtc = value.ToUniversalTime();
            }
        }

        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.LastAccessTimeUtc"]/*' />
        public DateTime LastAccessTimeUtc {
            get {
                if (_dataInitialised == -1) {
                    _data = new Native.FILE_ATTRIBUTE_DATA();
                    Refresh();
                }

                if (_dataInitialised != 0) // Refresh was unable to initialise the data
                    __Error.WinIOError(_dataInitialised, OriginalPath);

                return DateTime.FromFileTimeUtc(_data.ftLastAccessTime);

            }
            set {
                if (this is DirectoryInfo)
                    Directory.SetLastAccessTimeUtc(FullPath,value);
                else
                    File.SetLastAccessTimeUtc(FullPath,value);
                _dataInitialised = -1;
            }
        }

        public DateTime LastWriteTime {
            get {
                return LastWriteTimeUtc.ToLocalTime();
            }

            set {
                LastWriteTimeUtc = value.ToUniversalTime();
            }
        }

        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.LastWriteTimeUtc"]/*' />
        public DateTime LastWriteTimeUtc {
            get {
                if (_dataInitialised == -1) {
                    _data = new Native.FILE_ATTRIBUTE_DATA();
                    Refresh();
                }

                if (_dataInitialised != 0) // Refresh was unable to initialise the data
                    __Error.WinIOError(_dataInitialised, OriginalPath);

                return DateTime.FromFileTimeUtc(_data.ftLastWriteTime);
            }
            set {
                if (this is DirectoryInfo)
                    Directory.SetLastWriteTimeUtc(FullPath,value);
                else
                    File.SetLastWriteTimeUtc(FullPath,value);
                _dataInitialised = -1;
            }
        }

        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.Refresh"]/*' />
        public void Refresh()
        {
            _dataInitialised = File.FillAttributeInfo(FullPath,ref _data);
        }

        //| <include file='doc\FileSystemInfo.uex' path='docs/doc[@for="FileSystemInfo.GetAttributes"]/*' />
        public FileAttributes GetAttributes {
            get {
                if (_dataInitialised == -1) {
                    _data = new Native.FILE_ATTRIBUTE_DATA();
                    Refresh(); // Call refresh to initialise the data
                }

                if (_dataInitialised != 0) // Refresh was unable to initialise the data
                    __Error.WinIOError(_dataInitialised, OriginalPath);

                return (FileAttributes) _data.fileAttributes;
            }
            set {
                bool r = Native.SetFileAttributes(FullPath, (int) value);
                if (!r) {
                    __Error.WinIOError(0, OriginalPath);
                }
                _dataInitialised = -1;
            }
        }
    }
}

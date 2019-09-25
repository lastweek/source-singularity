// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Path
//
// Purpose: A collection of path manipulation methods.
//
//===========================================================  

using System;
using System.Text;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Globalization;

namespace System.IO
{
    // Provides methods for processing directory strings in an ideally
    // cross-platform manner.  Most of the methods don't do a complete
    // full parsing (such as examining a UNC hostname), but they will
    // handle most string operations.
    //
    // File names cannot contain backslash (\), slash (/), colon (:),
    // asterisk (*), question mark (?), quote ("), less than (<),
    // greater than (>), or pipe (|).  The first three are used as directory
    // separators on various platforms.  Asterisk and question mark are treated
    // as wild cards.  Less than, Greater than, and pipe all redirect input
    // or output from a program to a file or some combination thereof.  Quotes
    // are special.
    //
    // We are guaranteeing that Path.SeparatorChar is the correct
    // directory separator on all platforms, and we will support
    // Path.AltSeparatorChar as well.  To write cross platform
    // code with minimal pain, you can use slash (/) as a directory separator in
    // your strings.
    // Class contains only static data, no need to serialize
    //| <include file='doc\Path.uex' path='docs/doc[@for="Path"]/*' />
    public sealed class Path
    {

        private Path() {
        }

        // Platform specific directory separator character.  This is backslash
        // ('\') on Windows, slash ('/') on Unix, and colon (':') on Mac.
        //
        // @TODO porting: Make this platform specific when we port.
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.DirectorySeparatorChar"]/*' />
        public static readonly char DirectorySeparatorChar = '/';

        // Platform specific alternate directory separator character.
        // This is backslash ('\') on Unix, and slash ('/') on Windows
        // and MacOS.
        //
        // @TODO porting: Make this platform specific when we port.
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.AltDirectorySeparatorChar"]/*' />
        public static readonly char AltDirectorySeparatorChar = '\\';

        // Platform specific volume separator character.  This is colon (':')
        // on Windows and MacOS, and slash ('/') on Unix.  This is mostly
        // useful for parsing paths like "c:\windows" or "MacVolume:System Folder".
        //
        // @TODO porting: Make this platform specific when we port.
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.VolumeSeparatorChar"]/*' />
        public static readonly char VolumeSeparatorChar = ':';

        // Platform specific invalid list of characters in a path.
        //
        // @TODO porting: Make this platform specific when we port.
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.InvalidPathChars"]/*' />
        public static readonly char[] InvalidPathChars = { '\"', '<', '>', '|', '\0', '\b', (Char)16, (Char)17, (Char)18, (Char)20, (Char)21, (Char)22, (Char)23, (Char)24, (Char)25 };

        internal static readonly char[] InternalInvalidPathChars = { '\"', '<', '>', '|', '\0', '\b', (Char)16, (Char)17, (Char)18, (Char)20, (Char)21, (Char)22, (Char)23, (Char)24, (Char)25 };

        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.PathSeparator"]/*' />
        public static readonly char PathSeparator = ';';


        // Changes the extension of a file path. The path parameter
        // specifies a file path, and the extension parameter
        // specifies a file extension (with a leading period, such as
        // ".exe" or ".cool").
        //
        // The function returns a file path with the same root, directory, and base
        // name parts as path, but with the file extension changed to
        // the specified extension. If path is null, the function
        // returns null. If path does not contain a file extension,
        // the new file extension is appended to the path. If extension
        // is null, any existing extension is removed from path.
        //
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.ChangeExtension"]/*' />
        public static String ChangeExtension(String path, String extension) {
            if (path != null) {
                CheckInvalidPathChars(path);

                String s = path;
                for (int i = path.Length; --i >= 0;) {
                    char ch = path[i];
                    if (ch == '.') {
                        s = path.Substring(0, i);
                        break;
                    }
                    if (ch == DirectorySeparatorChar || ch == AltDirectorySeparatorChar || ch == VolumeSeparatorChar) break;
                }
                if (extension != null && path.Length != 0) {
                    if (extension.Length == 0 || extension[0] != '.') {
                        s = s + ".";
                    }
                    s = s + extension;
                }
                return s;
            }
            return null;
        }


        // Returns the directory path of a file path. This method effectively
        // removes the last element of the given file path, i.e. it returns a
        // string consisting of all characters up to but not including the last
        // backslash ("\") in the file path. The returned value is null if the file
        // path is null or if the file path denotes a root (such as "\", "C:", or
        // "\\server\share").
        //
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.GetDirectoryName"]/*' />
        public static String GetDirectoryName(String path) {
            if (path != null) {
                CheckInvalidPathChars(path);
                int root = GetRootLength(path);
                int i = path.Length;
                if (i > root) {
                    i = path.Length;
                    if (i == root) return null;
                    while (i > root && path[--i] != DirectorySeparatorChar && path[i] != AltDirectorySeparatorChar);
                    return path.Substring(0, i);
                }
            }
            return null;
        }

        // Gets the length of the root DirectoryInfo or whatever DirectoryInfo markers
        // are specified for the first part of the DirectoryInfo name.
        //
        internal static int GetRootLength(String! path) {
            CheckInvalidPathChars(path);

            int i = 0;
            int length = path.Length;
            if (length >= 1 && (IsDirectorySeparator(path[0]))) {
                // handles UNC names and directories off current drive's root.
                i = 1;
                if (length >= 2 && (IsDirectorySeparator(path[1]))) {
                    i = 2;
                    int n = 2;
                    while (i < length && ((path[i] != DirectorySeparatorChar && path[i] != AltDirectorySeparatorChar) || --n > 0)) i++;
                }
            }
            else if (length >= 2 && path[1] == VolumeSeparatorChar) {
                // handles A:\foo.
                i = 2;
                if (length >= 3 && (IsDirectorySeparator(path[2]))) i++;
            }
            return i;
        }

        internal static bool IsDirectorySeparator(char c) {
            return (c==DirectorySeparatorChar || c == AltDirectorySeparatorChar);
        }


        // Returns the extension of the given path. The returned value includes the
        // period (".") character of the extension except when you have a terminal period when you get String.Empty, such as ".exe" or
        // ".cpp". The returned value is null if the given path is
        // null or if the given path does not include an extension.
        //
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.GetExtension"]/*' />
        public static String GetExtension(String path) {
            if (path == null)
                return null;

            CheckInvalidPathChars(path);
            int length = path.Length;
            for (int i = length; --i >= 0;) {
                char ch = path[i];
                if (ch == '.') {
                    if (i != length - 1)
                        return path.Substring(i, length - i);
                    else
                        return String.Empty;
                }
                if (ch == DirectorySeparatorChar || ch == AltDirectorySeparatorChar || ch == VolumeSeparatorChar)
                    break;
            }
            return String.Empty;
        }

        // Expands the given path to a fully qualified path. The resulting string
        // consists of a drive letter, a colon, and a root relative path. This
        // function does not verify that the resulting path is valid or that it
        // refers to an existing file or DirectoryInfo on the associated volume.
        //
        // Your application must have unrestricted Environment permission.
        //

        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.GetFullPath"]/*' />
        public static String! GetFullPath(String! path) {
            String fullPath = GetFullPathInternal(path);
            return fullPath;
        }

        // This method is internal to let us quickly get a string name
        // while avoiding a security check.  This also serves a slightly
        // different purpose - when we open a file, we need to resolve the
        // path into a fully qualified, non-relative path name.  This
        // method does that, finding the current drive & directory.  But
        // as long as we don't return this info to the user, we're good.  However,
        // the public GetFullPath does need to do a security check.
        internal static String! GetFullPathInternal(String! path) {
            if (path == null) {
                throw new ArgumentNullException("path");
            }
            // BUGBUG: We removed a comparison for URI prefixes
            String newPath;
            int hresult = nGetFullPathHelper(path,
                                             InternalInvalidPathChars,
                                             new char[] {' '},
                                             DirectorySeparatorChar,
                                             AltDirectorySeparatorChar,
                                             true,
                                             out newPath);
            if (hresult != 0 || newPath == null) {
                __Error.WinIOError(hresult, path);
                assume false; // never get here
            }
            newPath = newPath.TrimStart();
            return newPath.ToLower();
        }

        internal static int nGetFullPathHelper(String! path,
                                               char[]! invalidPathChars,
                                               char[]! whitespaceChars,
                                               char directorySeparator,
                                               char altDirectorySeparator,
                                               char volumeSeparator,
                                               bool fullCheck,
                                               out String newPath) {
            return nGetFullPathHelper(path,invalidPathChars,whitespaceChars,directorySeparator,
                                      altDirectorySeparator,fullCheck,out newPath);
        }

        internal static int nGetFullPathHelper(String! path,
                                               char[]! invalidPathChars,
                                               char[]! whitespaceChars,
                                               char directorySeparator,
                                               char altDirectorySeparator,
                                               bool fullCheck,
                                               out String newPath) {
            int pathLength = path.Length;
            if (pathLength >= MAX_PATH) {
                throw new PathTooLongException("Max is "+MAX_PATH+" characters");
            }
            int whiteCount = whitespaceChars.Length;
            if (fullCheck) {
                while (pathLength > 0) {
                    bool foundMatch = false;
                    char lastChar = path[pathLength-1];
                    for (int whiteIndex = 0; whiteIndex < whiteCount; whiteIndex++) {
                        if (lastChar == whitespaceChars[whiteIndex]) {
                            foundMatch = true;
                            break;
                        }
                    }
                    if (!foundMatch) {
                        break;
                    }
                    pathLength--;
                }
            }
            if (pathLength == 0) {
                throw new ArgumentException("Empty path");
            }
            int invalidCount = invalidPathChars.Length;
            if (fullCheck) {
                for (int index = 0; index < pathLength; index++) {
                    char currentChar = path[index];
                    for (int invalidIndex = 0; invalidIndex < invalidCount; invalidIndex++) {
                        if (currentChar == invalidPathChars[invalidIndex]) {
                            throw new ArgumentException("Path has invalid character");
                        }
                    }
                }
            }
            int numDots = 0;
            int numSpaces = 0;
            bool fixupDirectorySeparator = false;
            bool fixupDotSeparator = true;
            int currentIndex = 0;
            char[] newBuffer = new char[pathLength+1];
            int newBufferIndex = 0;
            if (path[0] == '/' || path[0] == '\\') {
                newBuffer[newBufferIndex] = '/';
                newBufferIndex++;
                currentIndex++;
            }
            while (currentIndex < pathLength) {
                char currentChar = path[currentIndex];
                if (currentChar == directorySeparator ||
                    currentChar == altDirectorySeparator) {
                    if (fixupDotSeparator && numDots > 2) {
                        numDots = 2;
                    }
                    for (int count = 0; count < numDots; count++) {
                        newBuffer[newBufferIndex] = '.';
                        newBufferIndex++;
                    }
                    numSpaces = 0;
                    numDots = 0;
                    fixupDotSeparator = true;
                    if (!fixupDirectorySeparator) {
                        fixupDirectorySeparator = true;
                        newBuffer[newBufferIndex] = directorySeparator;
                        newBufferIndex++;
                    }
                }
                else if (currentChar == '.' && fixupDotSeparator) {
                    numDots++;
                    fixupDirectorySeparator = false;
                    numSpaces = 0;
                }
                else {
                    fixupDirectorySeparator = false;
                    if (currentChar == ' ') {
                        numSpaces++;
                    }
                    else {
                        for (int count = 0; count < numDots; count++) {
                            newBuffer[newBufferIndex] = '.';
                            newBufferIndex++;
                        }
                        numDots = 0;
                        fixupDotSeparator = false;
                        for (int count = 0; count < numSpaces; count++) {
                            newBuffer[newBufferIndex] = ' ';
                            newBufferIndex++;
                        }
                        numSpaces = 0;
                        newBuffer[newBufferIndex] = currentChar;
                        newBufferIndex++;
                    }
                }
                currentIndex++;
            }
            if (fixupDotSeparator && numDots > 2) {
                numDots = 2;
            }
            for (int count = 0; count < numDots; count++) {
                newBuffer[newBufferIndex] = '.';
                newBufferIndex++;
            }
            if (newBufferIndex == 0) {
                throw new ArgumentException("Empty path");
            }
            newBuffer[newBufferIndex] = '\0';
            if (newBuffer[0] == '\\' && newBuffer[1] == '\\') {
                int startIndex = 2;
                while (startIndex < newBufferIndex) {
                    if (newBuffer[startIndex] == '/') {
                        startIndex++;
                        break;
                    }
                    else {
                        startIndex++;
                    }
                }
                if (startIndex == newBufferIndex) {
                    throw new ArgumentException("UNC path without share name");
                }
            }
            if (fullCheck) {
                System.Text.StringBuilder resultBuffer =
                    new System.Text.StringBuilder(MAX_PATH+1);
                String initialPath =
                    String.StringCTOR(newBuffer, 0, newBufferIndex);
                int expandedLength = Native.GetFullPathName(initialPath,
                                                            MAX_PATH+1,
                                                            resultBuffer);
                if (expandedLength >= MAX_PATH) {
                    throw new PathTooLongException("FullPath is too long");
                }
                if (expandedLength == 0) {
                    newPath = null;
                    return -1;
                }
                newPath = resultBuffer.ToString();
            }
            else {
                newPath = String.StringCTOR(newBuffer, 0, newBufferIndex);
            }
            return 0;
        }

        // Returns the name and extension parts of the given path. The resulting
        // string contains the characters of path that follow the last
        // backslash ("\"), slash ("/"), or colon (":") character in
        // path. The resulting string is the entire path if path
        // contains no backslash after removing trailing slashes, slash, or colon characters. The resulting
        // string is null if path is null.
        //
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.GetFileName"]/*' />
        public static String GetFileName(String path) {
            if (path != null) {
                CheckInvalidPathChars(path);

                int length = path.Length;
                for (int i = length; --i >= 0;) {
                    char ch = path[i];
                    if (ch == DirectorySeparatorChar || ch == AltDirectorySeparatorChar || ch == VolumeSeparatorChar)
                        return path.Substring(i + 1, length - i - 1);

                }
            }
            return path;
        }

        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.GetFileNameWithoutExtension"]/*' />
        public static String GetFileNameWithoutExtension(String path) {
            path = GetFileName(path);
            if (path != null) {
                int i;
                if ((i = path.LastIndexOf('.')) == -1)
                    return path; // No path extension found
                else
                    return path.Substring(0,i);
            }
            return null;
        }



        // Returns the root portion of the given path. The resulting string
        // consists of those rightmost characters of the path that constitute the
        // root of the path. Possible patterns for the resulting string are: An
        // empty string (a relative path on the current drive), "\" (an absolute
        // path on the current drive), "X:" (a relative path on a given drive,
        // where X is the drive letter), "X:\" (an absolute path on a given drive),
        // and "\\server\share" (a UNC path for a given server and share name).
        // The resulting string is null if path is null.
        //
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.GetPathRoot"]/*' />
        public static String GetPathRoot(String path) {
            if (path == null) return null;
            return path.Substring(0, GetRootLength(path));
        }

        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.GetTempPath"]/*' />
        public static String GetTempPath()
        {
            StringBuilder sb = new StringBuilder(MAX_PATH);
            uint r = Native.GetTempPath(MAX_PATH, sb);
            String path = sb.ToString();
            if (r == 0) __Error.WinIOError();
            return path;
        }

        // Returns a unique temporary file name, and creates a 0-byte file by that
        // name on disk.
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.GetTempFileName"]/*' />
        public static String GetTempFileName()
        {
            String path = GetTempPath();
            StringBuilder sb = new StringBuilder(MAX_PATH);
            uint r = Native.GetTempFileName(path, "tmp", 0, sb);
            if (r == 0) __Error.WinIOError();
            return sb.ToString();
        }

        // Tests if a path includes a file extension. The result is
        // true if the characters that follow the last directory
        // separator ('\\' or '/') or volume separator (':') in the path include
        // a period (".") other than a terminal period. The result is false otherwise.
        //
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.HasExtension"]/*' />
        public static bool HasExtension(String path) {
            if (path != null) {
                CheckInvalidPathChars(path);

                for (int i = path.Length; --i >= 0;) {
                    char ch = path[i];
                    if (ch == '.') {
                        if (i != path.Length - 1)
                            return true;
                        else
                            return false;
                    }
                    if (ch == DirectorySeparatorChar || ch == AltDirectorySeparatorChar || ch == VolumeSeparatorChar) break;
                }
            }
            return false;
        }


        // Tests if the given path contains a root. A path is considered rooted
        // if it starts with a backslash ("\") or a drive letter and a colon (":").
        //
        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.IsPathRooted"]/*' />
        public static bool IsPathRooted(String path) {
            if (path != null) {
                CheckInvalidPathChars(path);

                int length = path.Length;
                if (length >= 1 && (path[0] == DirectorySeparatorChar || path[0] == AltDirectorySeparatorChar) ||
                    length >= 2 && path[1] == VolumeSeparatorChar) return true;
            }
            return false;
        }

        //| <include file='doc\Path.uex' path='docs/doc[@for="Path.Combine"]/*' />
        public static String Combine(String path1, String path2) {
            if (path1 == null || path2 == null)
                throw new ArgumentNullException((path1==null) ? "path1" : "path2");
            CheckInvalidPathChars(path1);
            CheckInvalidPathChars(path2);

            if (path2.Length == 0)
                return path1;

            if (path1.Length == 0)
                return path2;

            if (IsPathRooted(path2))
                return path2;

            char ch = path1[path1.Length - 1];
            if (ch != DirectorySeparatorChar && ch != AltDirectorySeparatorChar && ch != VolumeSeparatorChar)
                return path1 + DirectorySeparatorChar + path2;
            return path1 + path2;
        }


        internal static void CheckInvalidPathChars(String! path)
        {
            //if (path==null)
            //  return;
            if (-1 != path.IndexOfAny(InternalInvalidPathChars))
                throw new ArgumentException("Argument_InvalidPathChars");
        }


        internal static String! InternalCombine(String path1, String path2) {
            if (path1 == null || path2 == null)
                throw new ArgumentNullException((path1==null) ? "path1" : "path2");
            CheckInvalidPathChars(path1);
            CheckInvalidPathChars(path2);

            if (path2.Length == 0)
                throw new ArgumentException("Argument_PathEmpty", "path2");
            if (IsPathRooted(path2))
                throw new ArgumentException("Arg_Path2IsRooted", "path2");
            int i = path1.Length;
            if (i == 0) return path2;
            char ch = path1[i - 1];
            if (ch != DirectorySeparatorChar && ch != AltDirectorySeparatorChar && ch != VolumeSeparatorChar)
                return path1 + DirectorySeparatorChar + path2;
            return path1 + path2;
        }

        // Windows API definitions
        internal const int MAX_PATH = 260;  // From WinDef.h
        internal const int ERROR_SUCCESS = 0;  // From WinError.h
        internal const int MAX_DIRECTORY_PATH = 248;   // cannot create directories greater than 248 characters
    }
}

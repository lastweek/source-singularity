///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   mkflash.cs
//
//  Note:   Flash image building tool.
//

using System;
using System.Collections;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.IO;
using System.Text;
using System.Threading;

#if SINGULARITY
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity;
using Microsoft.Singularity.Applications;
#endif

namespace Microsoft.Singularity.Applications
{
    public class ContentFile
    {
        public ContentFile(string prefix, string path)
        {
            FileInfo fileInfo = new FileInfo(prefix + path);

            this.Path = path;
            this.Size = (uint)fileInfo.Length;

            DataOffset = 0;
            PathOffset = 0;
        }

        public ContentFile(string path, uint size)
        {
            this.Path = path;
            this.Size = size;

            DataOffset = 0;
            PathOffset = 0;
        }

        // FileInfo fileInfo = new FileInfo(originalFilePath);
        // using (FileStream fs = fileInfo.OpenRead()) {
        public readonly string  Path;
        public readonly uint    Size;
        public uint             DataOffset;
        public uint             PathOffset;

        private static string ParseParameter(string line, string param)
        {
            int beg = line.IndexOf(param);
            if (beg >= 0) {
                string rest = line.Substring(beg + param.Length);

                int end = rest.IndexOf(' ');
                if (end >= 0) {
                    return rest.Substring(0, end);
                }
                return rest;
            }
            return null;
        }

        public static ContentFile[] ReadFilesFromFile(string filePath)
        {
            ArrayList inFiles = new ArrayList();

            try {
                using (StreamReader sr = new StreamReader(filePath)) {
                    string line;
                    int count = 0;
                    while ((line = sr.ReadLine()) != null) {
                        ++count;
                        line = line.Trim();
                        if (line.Length == 0 || line[0] == '#') {
                            // Skip blank and comment lines.
                            continue;
                        }

                        string path = ParseParameter(line, "Path=");
                        string sizs = ParseParameter(line, "Size=");
                        string hash = ParseParameter(line, "Hash-MD5=");
                        uint size = UInt32.Parse(sizs);

                        if (path == null || path == "" || size == 0) {
                            Console.WriteLine("mkflash: Error: {0}#{1} missing path or size.",
                                              filePath, count);
                            continue;
                        }
                        inFiles.Add(new ContentFile(path, size));
                    }
                }

                return (ContentFile[])inFiles.ToArray(typeof(ContentFile));
            }
            catch (FileNotFoundException) {
                Console.WriteLine("File not found {0}\n", filePath);
                return null;
            }
        }
    }

    public class NativeImageBuilder
    {
        public const uint FLASH_HEAD_SIZE   = 32;
        public const uint FLASH_FILE_SIZE   = 12;

        //
        // Global flags.
        //
        public static bool Verbose = false;

        // Print the correct command line args for the program
        static void Usage()
        {
            Console.WriteLine(
                "Usage:\n" +
                "    mkflash [options] /flash:<file> /root:<path> /boot:<file>\n" +
                "Options:\n" +
                "    /flash:<file>       - Name of target flash image.\n" +
                "    /root:<path>        - Root of file distro.\n" +
                "    /boot:<file>        - Singboot.ini file listing files for image.\n" +
                "Summary:\n" +
                "    Create a flash image image for a distribution.\n" +
                "");
        }

        static bool IsQuote(char c)
        {
            return (c == '"' || c == '\'');
        }

        static string RemoveQuotes(string text)
        {
            int start = 0;
            int length = text.Length;

            if (length > 0 && IsQuote(text[start + length - 1])) {
                length--;
            }
            if (length > 0 && IsQuote(text[start])) {
                start++;
                length--;
            }

            if (start != 0 || length != text.Length) {
                return text.Substring(start, length);
            }
            else {
                return text;
            }
        }

        static bool StringIsNullOrEmpty(string str)
        {
            return (str == null || str.Length == 0);
        }

        static uint PadToPage(uint value)
        {
            return (value + 0xfffu) & ~0xfffu;
        }

        static uint FileRecord(uint file)
        {
            return FLASH_HEAD_SIZE + FLASH_FILE_SIZE * file;
        }

        static void WriteUInt32(byte[] buffer, uint offset, uint value)
        {
            buffer[offset + 0] = (byte)((value & 0x000000ff) >> 0);
            buffer[offset + 1] = (byte)((value & 0x0000ff00) >> 8);
            buffer[offset + 2] = (byte)((value & 0x00ff0000) >> 16);
            buffer[offset + 3] = (byte)((value & 0xff000000) >> 24);
        }

        static uint WriteString(byte[] buffer, uint offset, String value)
        {
            for (int i = 0; i < value.Length; i++) {
                buffer[offset + i] = (byte)value[i];
            }
            buffer[offset + value.Length] = 0;
            return (uint)value.Length + 1;
        }

        static uint Copy(byte[] buffer, FileStream ostream, FileStream istream, uint size)
        {
            uint written = 0;
            while (size > buffer.Length) {
                istream.Read(buffer, 0, buffer.Length);
                ostream.Write(buffer, 0, buffer.Length);
                size -= (uint)buffer.Length;
                written += (uint)buffer.Length;
            }
            if (size > 0) {
                istream.Read(buffer, 0, (int)size);
                for (int pad = (int)PadToPage((uint)size); size < pad; size++) {
                    buffer[size] = 0xff;
                }
                ostream.Write(buffer, 0, (int)size);
                written += size;
            }
            return written;
        }

        static int Main(string[] args)
        {
            ContentFile[] inFiles = null;
            string flashImage = null;
            string rootDirectory = null;

            // Temporaries for command-line parsing
            bool needHelp = (args.Length == 0);

#if !SINGULARITY
            for (int i = 0; i < args.Length && !needHelp; i++) {
#else
            for (int i = 1; i < args.Length && !needHelp; i++) {
#endif
                string arg = (string) args[i];
                arg = RemoveQuotes(arg);

                if (arg.Length >= 2 && (arg[0] == '-' || arg[0] == '/')) {
                    string name = null;
                    string value = null;
                    int n = arg.IndexOf(':');
                    if (n > -1) {
                        name = arg.Substring(1, n - 1).ToLower();
                        if (n < arg.Length + 1) {
                            value = arg.Substring(n + 1);
                        }
                    }
                    else {
                        name = arg.Substring(1).ToLower();
                    }
                    if (value != null) {
                        value = value.Trim();
                        value = RemoveQuotes(value);
                        value = value.Trim();
                    }

                    bool badArg = false;
                    switch (name) {
                        case "h":
                        case "help":
                        case "?":
                            needHelp = true;
                            break;

                        case "file":
                            inFiles = new ContentFile[]
                                { new ContentFile(rootDirectory, value) };
                            break;

                        case "boot":
                        case "bootfile":
                            if (value != null) {
                                if ((inFiles = ContentFile.ReadFilesFromFile(value)) == null) {
                                    return 3;
                                }
                            }
                            else {
                                badArg = true;
                            }
                            break;

                        case "flash":
                            if (value != null) {
                                flashImage = value;
                            }
                            else {
                                badArg = true;
                            }
                            break;

                        case "root":
                            if (value != null) {
                                rootDirectory = value.TrimEnd('/', '\\');
                            }
                            else {
                                badArg = true;
                            }
                            break;

                        case "v":
                            Verbose = true;
                            break;

                        default:
                            Console.WriteLine("mkflash: Unknown command line argument: {0}", arg);
                            needHelp = true;
                            break;
                    }
                    if (badArg) {
                        Console.WriteLine("mkflash: Invalid command line argument: {0}", arg);
                        needHelp = true;
                    }
                }
                else {
                    Console.WriteLine("mkflash: Invalid command line argument: {0}", arg);
                    needHelp = true;
                }
            }

            if (inFiles == null || inFiles.Length == 0) {
                Console.WriteLine("mkflash: /boot:<file> missing from command line.");
                needHelp = true;
            }

            if (rootDirectory == null) {
                Console.WriteLine("mkflash: /root:<path> missing from command line.");
                needHelp = true;
            }
            if (flashImage == null) {
                Console.WriteLine("mkflash: /flash:<path> missing from command line.");
                needHelp = true;
            }

            if (needHelp) {
                Usage();
                return 1;
            }

            // check all input files
            if (!Directory.Exists(rootDirectory)) {
                Console.WriteLine("mkflash: Error: Root directory '{0}' not found.",
                                  rootDirectory);
                return 2;
            }

            // check all input files
            for (int i = 0; i < inFiles.Length; i++) {
                if (!File.Exists(rootDirectory + inFiles[i].Path)) {
                    Console.WriteLine("mkflash: Error: Application manifest '{0}' not found.",
                                      rootDirectory + inFiles[i].Path);
                    return 2;
                }
            }

            // check that we can create the output file.
            byte[] buffer = new byte [256 * 1024];
            try {
                FileStream stream = new FileStream(flashImage, FileMode.Create);
                if (stream == null) {
                    throw new IOException("Why is this null?");
                }

                // Write the flash header.
                // Save room for extra files.
                buffer[0] = (byte)'S';
                buffer[1] = (byte)'i';
                buffer[2] = (byte)'n';
                buffer[3] = (byte)'g';
                buffer[4] = (byte)'u';
                buffer[5] = (byte)'l';
                buffer[6] = (byte)'a';
                buffer[7] = (byte)'r';
                buffer[8] = (byte)'i';
                buffer[9] = (byte)'t';
                buffer[10] = (byte)'y';
                buffer[11] = (byte)'F';
                buffer[12] = (byte)'l';
                buffer[13] = (byte)'a';
                buffer[14] = (byte)'s';
                buffer[15] = (byte)'h';
                buffer[16] = (byte)'!';
                buffer[17] = 0;
                buffer[18] = (byte)FLASH_HEAD_SIZE;
                buffer[19] = (byte)FLASH_FILE_SIZE;
                WriteUInt32(buffer, 20, 0x1000);    // Page size.
                WriteUInt32(buffer, 24, unchecked((uint)-1));
                WriteUInt32(buffer, 28, unchecked((uint)-1));
                uint head = PadToPage(FileRecord((uint)(2 * inFiles.Length)));

                for (uint pad = FileRecord((uint)inFiles.Length); pad < head; pad++) {
                    buffer[pad] = 0xff;
                }

                // Write the path names and save the path offsets.
                uint pathoff = head;
                for (int i = 0; i < inFiles.Length; i++) {
                    inFiles[i].PathOffset = pathoff;

                    pathoff += WriteString(buffer, inFiles[i].PathOffset, inFiles[i].Path);
                }
                // Save room for extra path names.
                uint data = PadToPage(head + (pathoff - head) * 2);
                head = data;

                // Calculate the file data offsets.
                for (int i = 0; i < inFiles.Length; i++) {
                    inFiles[i].DataOffset = head;
                    head += PadToPage(inFiles[i].Size);
                }

                // Write the file records.
                uint offset;
                for (uint i = 0; i < inFiles.Length; i++) {
                    offset = FileRecord(i);
                    WriteUInt32(buffer, offset + 0, inFiles[i].PathOffset);
                    WriteUInt32(buffer, offset + 4, inFiles[i].DataOffset);
                    WriteUInt32(buffer, offset + 8, inFiles[i].Size);
                }

                // Terminate the list.
                offset = FileRecord((uint)(2 * inFiles.Length - 1));
                WriteUInt32(buffer, offset + 0, 0);
                WriteUInt32(buffer, offset + 4, 0xffffffff);
                WriteUInt32(buffer, offset + 8, 0);

                if (Verbose) {
                    Console.WriteLine("  {0,8:x}..{1,8:x}: Header", 0, data - 1);
                }
                stream.Write(buffer, 0, (int)data);

                // Write each file.
                for (int i = 0; i < inFiles.Length; i++) {
                    string file = rootDirectory + inFiles[i].Path;
                    FileStream istream = new FileStream(file, FileMode.Open);
                    if (istream == null) {
                        throw new IOException("Why is this null?");
                    }

                    uint written = Copy(buffer, stream, istream, inFiles[i].Size);
                    if (Verbose) {
                        Console.WriteLine("  {0,8:x}..{1,8:x}: {2,8:x} {3}",
                                          inFiles[i].DataOffset,
                                          inFiles[i].DataOffset + written - 1,
                                          inFiles[i].PathOffset,
                                          inFiles[i].Path);
                    }

                    istream.Close();
                }
                stream.Close();
            }
            catch (IOException ex) {
                for (Exception current = ex; current != null; current = current.InnerException) {
                    Console.WriteLine("mkflash: Error: {0}", current.Message);
                }
                try {
                    File.Delete(flashImage);
                }
                catch (Exception) {
                }
                return 4;
            }
            return 0;
        }
    }
}

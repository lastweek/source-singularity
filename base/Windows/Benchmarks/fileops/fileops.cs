// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Runtime.InteropServices;
using System.Text;
using webfiles; 

namespace webfiles
{

    class FileReader
    {
        //const uint FILE_FLAG_NO_BUFFERING = 0x20000000;
        const uint FILE_FLAG_NO_BUFFERING = 0;
        const uint GENERIC_READ = 0x80000000;
        const uint OPEN_EXISTING = 3;
        IntPtr handle;

        [DllImport("kernel32", SetLastError=true)]
        private static extern unsafe IntPtr CreateFile(
            string FileName,                    // file name
            uint DesiredAccess,                 // access mode
            uint ShareMode,                     // share mode
            uint SecurityAttributes,            // Security Attributes
            uint CreationDisposition,           // how to create
            uint FlagsAndAttributes,            // file attributes
            int hTemplateFile                   // handle to template file
            );

        [DllImport("kernel32", SetLastError=true)]
        private static extern unsafe bool ReadFile(
            IntPtr hFile,                       // handle to file
            void* pBuffer,                      // data buffer
            int NumberOfBytesToRead,            // number of bytes to read
            int* pNumberOfBytesRead,            // number of bytes read
            int Overlapped                      // overlapped buffer
            );

        [DllImport("kernel32", SetLastError=true)]
        private static extern unsafe bool CloseHandle(
            IntPtr hObject                      // handle to object
            );

        [DllImport("kernel32", SetLastError=true)]
        private static extern unsafe uint GetFileSize(
            IntPtr hObject,                     // handle to object
            uint *pFileSizeHigh                 // receives high 32-bits of file size.
            );

        public bool Open(string FileName)
        {
            // open the existing file for reading
            handle = CreateFile(
                FileName,
                GENERIC_READ,
                0,
                0,
                OPEN_EXISTING, 
                FILE_FLAG_NO_BUFFERING,
                0);
            if (handle != IntPtr.Zero && handle != ((IntPtr) (-1))) {
                return true;
            }
            else {
                return false;
            }
        }

        public unsafe int Read(byte[] buffer, int index, int count)
        {
            int n = 0;
            fixed (byte* p = buffer) {
                if (!ReadFile(handle, p + index, count, &n, 0)) {
                    return 0;
                }
            }
            return n;
        }

        public bool Close()
        {
            // close file handle
            return CloseHandle(handle);
        }

        public unsafe int Size()
        {
            return (int)GetFileSize(handle, null);
        }
    }
    
    public class SpecMain
    {
        //--------------------------------------------------
        // Main routine
        //--------------------------------------------------
        public static int Main(string[] args)
        {
            FileReader reader = new  FileReader(); 
            
            DateTime start =  DateTime.Now; 
            
            for (int i = 1; i < 1000; i++) {
                if (!reader.Open(args[0])) {
                    Console.WriteLine("Failed"); 
                    throw new Exception("argh.."); 
                }
                reader.Close(); 
            }
            DateTime  end =  DateTime.Now;
            TimeSpan elapsed = end - start; 
            
            Console.WriteLine("5000 iterations = {0}",elapsed); 
             return 0;
        } // main
    } //specmain class}
}

// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  FileNotFoundException
//
// Purpose: Exception for accessing a file that doesn't exist.
//
//===========================================================  

using System;

namespace System.IO
{
    // Thrown when trying to access a file that doesn't exist on disk.
    //| <include file='doc\FileNotFoundException.uex' path='docs/doc[@for="FileNotFoundException"]/*' />
    public class FileNotFoundException : IOException {

        private String _fileName;  // The name of the file that isn't found.

        //| <include file='doc\FileNotFoundException.uex' path='docs/doc[@for="FileNotFoundException.FileNotFoundException"]/*' />
        public FileNotFoundException()
            : base("IO.FileNotFound") {
        }

        //| <include file='doc\FileNotFoundException.uex' path='docs/doc[@for="FileNotFoundException.FileNotFoundException1"]/*' />
        public FileNotFoundException(String message)
            : base(message) {
        }

        //| <include file='doc\FileNotFoundException.uex' path='docs/doc[@for="FileNotFoundException.FileNotFoundException2"]/*' />
        public FileNotFoundException(String message, Exception innerException)
            : base(message, innerException) {
        }

        //| <include file='doc\FileNotFoundException.uex' path='docs/doc[@for="FileNotFoundException.FileNotFoundException3"]/*' />
        public FileNotFoundException(String message, String fileName) : base(message)
        {
            _fileName = fileName;
        }

        //| <include file='doc\FileNotFoundException.uex' path='docs/doc[@for="FileNotFoundException.FileNotFoundException4"]/*' />
        public FileNotFoundException(String message, String fileName, Exception innerException)
            : base(message, innerException) {
            _fileName = fileName;
        }

        //| <include file='doc\FileNotFoundException.uex' path='docs/doc[@for="FileNotFoundException.Message"]/*' />
        public override String Message
        {
            get {
                String message = base.Message;
                if (message == null) {
                    if (_fileName == null)
                        return "IO.FileNotFound";
                    else
                        return "IO.FileNotFound" + _fileName;
                }
                else {
                    return message;
                }
            }
        }

        //| <include file='doc\FileNotFoundException.uex' path='docs/doc[@for="FileNotFoundException.FileName"]/*' />
        public String FileName {
            get { return _fileName; }
        }

        //| <include file='doc\FileNotFoundException.uex' path='docs/doc[@for="FileNotFoundException.ToString"]/*' />
        public override String ToString()
        {
            String s = GetType().FullName + ": " + Message;

            if (_fileName != null && _fileName.Length != 0)
                s += Environment.NewLine + String.Format("IO.FileName_Name", _fileName);

            if (InnerException != null)
                s = s + " ---> " + InnerException.ToString();

            return s;
        }
    }
}


// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  FileLoadException
//
// Purpose: Exception for failure to load a file that was successfully found.
//
//===========================================================  

using System;
using System.Runtime.CompilerServices;

namespace System.IO
{

    //| <include file='doc\FileLoadException.uex' path='docs/doc[@for="FileLoadException"]/*' />
    public class FileLoadException : IOException {

        private String _fileName;   // the name of the file we could not load.

        //| <include file='doc\FileLoadException.uex' path='docs/doc[@for="FileLoadException.FileLoadException"]/*' />
        public FileLoadException()
            : base("IO.FileLoad") {
        }

        //| <include file='doc\FileLoadException.uex' path='docs/doc[@for="FileLoadException.FileLoadException1"]/*' />
        public FileLoadException(String message)
            : base(message) {
        }

        //| <include file='doc\FileLoadException.uex' path='docs/doc[@for="FileLoadException.FileLoadException2"]/*' />
        public FileLoadException(String message, Exception inner)
            : base(message, inner) {
        }

        //| <include file='doc\FileLoadException.uex' path='docs/doc[@for="FileLoadException.FileLoadException3"]/*' />
        public FileLoadException(String message, String fileName) : base(message)
        {
            _fileName = fileName;
        }

        //| <include file='doc\FileLoadException.uex' path='docs/doc[@for="FileLoadException.FileLoadException4"]/*' />
        public FileLoadException(String message, String fileName, Exception inner)
            : base(message, inner) {
            _fileName = fileName;
        }

        //| <include file='doc\FileLoadException.uex' path='docs/doc[@for="FileLoadException.Message"]/*' />
        public override String Message
        {
            get {
                String message = base.Message;
                if (message == null) {
                    if (_fileName == null)
                        return "IO.FileLoad";
                    else
                        return "IO.FileLoad" + _fileName;
                }
                else {
                    return message;
                }
            }
        }

        //| <include file='doc\FileLoadException.uex' path='docs/doc[@for="FileLoadException.FileName"]/*' />
        public String FileName {
            get { return _fileName; }
        }

        //| <include file='doc\FileLoadException.uex' path='docs/doc[@for="FileLoadException.ToString"]/*' />
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

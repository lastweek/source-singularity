// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: Exception
//
// Purpose: The base class for all exceptional conditions.
//
//=============================================================================  

namespace System
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using System.Diagnostics;
    using System.Text;
    using System.Reflection;
#if SINGULARITY_KERNEL
    using Microsoft.Singularity;
#elif SINGULARITY_PROCESS
    using Microsoft.Singularity.V1.Services;
#endif // SINGULARITY_PROCESS


    //| <include path='docs/doc[@for="Exception"]/*' />
    [AccessedByRuntime("referenced from halexn.cpp")]
    public partial class Exception
    {
        //| <include path='docs/doc[@for="Exception.Exception"]/*' />
        public Exception() {
            _message = null;
#if SINGULARITY_KERNEL
            //DebugStub.Break();
#elif SINGULARITY_PROCESS
            //DebugService.Break();
#endif // SINGULARITY_PROCESS
        }

        [RequiredByBartok]
        public Exception(String message): this() {
            this._message = message;
        }

        // Creates a new Exception.  All derived classes should
        // provide this constructor.
        // Note: the stack trace is not started until the exception
        // is thrown
        //
        //| <include path='docs/doc[@for="Exception.Exception2"]/*' />
        public Exception (String message, Exception innerException)
        {
            // TODO: The innerException will be provided by the runtime
            // in the M9 time frame. Until then, we need this method.
            _message = message;
            _innerException = innerException;
        }

        //| <include path='docs/doc[@for="Exception.Message"]/*' />
        public virtual String Message {
               get {
                if (_message == null) {
                    return "Exception_WasThrown";
                }
                else {
                    return _message;
                }
            }
        }

        private String GetClassName() {
            return this.vtable.vtableType.FullName;
        }

        // Retrieves the lowest exception (inner most) for the given Exception.
        // This will traverse exceptions using the innerException property.
        //
        //| <include path='docs/doc[@for="Exception.GetBaseException"]/*' />
        public virtual Exception GetBaseException()
        {
            Exception inner = InnerException;
            Exception back = this;

            while (inner != null) {
                back = inner;
                inner = inner.InnerException;
            }

            return back;
        }

        // Returns the inner exception contained in this exception
        //
        //| <include path='docs/doc[@for="Exception.InnerException"]/*' />
        public Exception InnerException {
            get { return _innerException; }
        }

        //| <include path='docs/doc[@for="Exception.ToString"]/*' />
        public override String ToString() {
            String message = Message;

            if (_innerException != null) {
                message = message + " ---> " + _innerException.ToString() + "\r\n" + "   " + "Exception_EndOfInnerExceptionStack";
            }

            return message;
        }

        [AccessedByRuntime("referenced from halexn.cpp")]
        internal String _message;

        private Exception _innerException;

        [AccessedByRuntime("referenced from halexn.cpp")]
        private UIntPtr _throwAddress;

        [AccessedByRuntime("referenced from halexn.cpp")]
        private bool _notifiedDebugger; // True if debugger first chance already thrown.

        // [Bartok]:
        public string StackTrace
        {
            get {
                return "<no.stack.trace>";
            }
        }
    }
}

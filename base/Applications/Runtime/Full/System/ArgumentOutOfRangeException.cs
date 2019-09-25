// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: ArgumentOutOfRangeException
//
// Purpose: Exception class for method arguments outside of the legal range.
//
//=============================================================================  

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    // The ArgumentOutOfRangeException is thrown when an argument
    // is outside the legal range for that argument.  This may often be caused
    // by
    //
    //| <include path='docs/doc[@for="ArgumentOutOfRangeException"]/*' />
    public partial class ArgumentOutOfRangeException : ArgumentException {

        private static String _rangeMessage;
        private Object m_actualValue;

        private static String RangeMessage {
            get {
                if (_rangeMessage == null)
                    _rangeMessage = "Arg_ArgumentOutOfRangeException";
                return _rangeMessage;
            }
        }

        // Creates a new ArgumentOutOfRangeException with its message
        // string set to a default message explaining an argument was out of range.
        //| <include path='docs/doc[@for="ArgumentOutOfRangeException.ArgumentOutOfRangeException"]/*' />
        public ArgumentOutOfRangeException()
            : base(RangeMessage) {
        }

        //| <include path='docs/doc[@for="ArgumentOutOfRangeException.ArgumentOutOfRangeException1"]/*' />
        public ArgumentOutOfRangeException(String paramName)
            : base(RangeMessage, paramName) {
        }

        //| <include path='docs/doc[@for="ArgumentOutOfRangeException.ArgumentOutOfRangeException2"]/*' />
        public ArgumentOutOfRangeException(String paramName, String message)
            : base(message, paramName) {
        }

        // We will not use this in the classlibs, but we'll provide it for
        // anyone that's really interested so they don't have to stick a bunch
        // of printf's in their code.
        //| <include path='docs/doc[@for="ArgumentOutOfRangeException.ArgumentOutOfRangeException3"]/*' />
        public ArgumentOutOfRangeException(String paramName, Object actualValue, String message)
            : base(message, paramName) {
            m_actualValue = actualValue;
        }

        //| <include path='docs/doc[@for="ArgumentOutOfRangeException.Message"]/*' />
        public override String Message
        {
            get {
                String s = base.Message;
                if (m_actualValue != null) {
                    String valueMessage = String.Format("ArgumentOutOfRange_ActualValue", m_actualValue.ToString());
                    if (s == null)
                        return valueMessage;
                    return s + Environment.NewLine + valueMessage;
                }
                return s;
            }
        }

        // Gets the value of the argument that caused the exception.
        // Note - we don't set this anywhere in the class libraries in
        // version 1, but it might come in handy for other developers who
        // want to avoid sticking printf's in their code.
        //| <include path='docs/doc[@for="ArgumentOutOfRangeException.ActualValue"]/*' />
        public virtual Object ActualValue {
            get { return m_actualValue; }
        }
    }
}

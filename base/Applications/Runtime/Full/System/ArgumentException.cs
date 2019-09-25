// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: ArgumentException
//
// Purpose: Exception class for invalid arguments to a method.
//
//=============================================================================  

namespace System
{

    using System;

    // The ArgumentException is thrown when an argument does not meet
    // the contract of the method.  Ideally it should give a meaningful error
    // message describing what was wrong and which parameter is incorrect.
    //
    //| <include path='docs/doc[@for="ArgumentException"]/*' />
    public class ArgumentException : SystemException {
        private String m_paramName;

        // Creates a new ArgumentException with its message
        // string set to the empty string.
        //| <include path='docs/doc[@for="ArgumentException.ArgumentException"]/*' />
        public ArgumentException()
            : base("Arg_ArgumentException") {
        }

        // Creates a new ArgumentException with its message
        // string set to message.
        //
        //| <include path='docs/doc[@for="ArgumentException.ArgumentException1"]/*' />
        public ArgumentException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="ArgumentException.ArgumentException2"]/*' />
        public ArgumentException(String message, Exception innerException)
            : base(message, innerException) {
        }

        //| <include path='docs/doc[@for="ArgumentException.ArgumentException3"]/*' />
        public ArgumentException(String message, String paramName, Exception innerException)
            : base(message, innerException) {
            m_paramName = paramName;
        }

        //| <include path='docs/doc[@for="ArgumentException.ArgumentException4"]/*' />
        public ArgumentException(String message, String paramName)

            : base (message) {
            m_paramName = paramName;
        }

        //| <include path='docs/doc[@for="ArgumentException.Message"]/*' />
        public override String Message
        {
            get {
                String s = base.Message;
                if (!((m_paramName == null) ||
                       (m_paramName.Length == 0)) )
                    return s + Environment.NewLine + String.Format("{0}", m_paramName);
                else
                    return s;
            }
        }

        //
        //public String ToString()
        //{
        //  String s = super.ToString();
        //  if (m_paramName != null)
        //      return s + "Parameter name: "+m_paramName+"\tActual value: "+(m_actualValue==null ? "<null>" : m_actualValue.ToString());
        //  else
        //      return s;
        //}
        //

        //| <include path='docs/doc[@for="ArgumentException.ParamName"]/*' />
        public virtual String ParamName {
            get { return m_paramName; }
        }
    }
}

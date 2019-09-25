// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{
    using System;

    //| <include path='docs/doc[@for="ObjectDisposedException"]/*' />
    /// <devdoc>
    ///    <para> The exception that is thrown when accessing an object that was
    ///       disposed.</para>
    /// </devdoc>
    public class ObjectDisposedException : InvalidOperationException {
        private String objectName;

        //| <include path='docs/doc[@for="ObjectDisposedException.ObjectDisposedException"]/*' />
        /// <devdoc>
        /// <para>Initializes a new instance of the <see cref='System.ObjectDisposedException'/> class.</para>
        /// </devdoc>
        public ObjectDisposedException(String objectName) : base(String.Format("ObjectDisposed_Generic_ObjectName", objectName)) {
            this.objectName = objectName;
        }

        //| <include path='docs/doc[@for="ObjectDisposedException.ObjectDisposedException2"]/*' />
        /// <devdoc>
        /// <para>Initializes a new instance of the <see cref='System.ObjectDisposedException'/> class.</para>
        /// </devdoc>
        public ObjectDisposedException(String objectName, String message) : base(message) {
            this.objectName = objectName;
        }

        //| <include path='docs/doc[@for="ObjectDisposedException.Message"]/*' />
        /// <devdoc>
        ///    <para>Gets the text for the message for this exception.</para>
        /// </devdoc>
        public override String Message {
            get {
                String name = ObjectName;
                if (name == null || name.Length == 0)
                    return base.Message;
                return base.Message + Environment.NewLine + String.Format("ObjectDisposed_ObjectName_Name", name);
            }
        }

        //| <include path='docs/doc[@for="ObjectDisposedException.ObjectName"]/*' />
        public String ObjectName {
            get {
                if (objectName == null)
                    return String.Empty;
                return objectName;
            }
        }
    }
}

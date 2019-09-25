// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: SynchronizationLockException
//
// Purpose: Wait(), Notify() or NotifyAll() was called from an unsynchronized
//          block of code.
//
//=============================================================================  

namespace System.Threading
{

    using System;

    //| <include path='docs/doc[@for="SynchronizationLockException"]/*' />
    public class SynchronizationLockException : SystemException {
        //| <include path='docs/doc[@for="SynchronizationLockException.SynchronizationLockException"]/*' />
        public SynchronizationLockException()
            : base("Arg_SynchronizationLockException") {
        }

        //| <include path='docs/doc[@for="SynchronizationLockException.SynchronizationLockException1"]/*' />
        public SynchronizationLockException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="SynchronizationLockException.SynchronizationLockException2"]/*' />
        public SynchronizationLockException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}



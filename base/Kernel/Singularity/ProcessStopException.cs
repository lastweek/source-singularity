//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Microsoft.Singularity 
{
    using System;

    // The kernel throws a ProcessStopException to stop the current
    // thread (as part of stopping a whole process).  This is not
    // thrown asynchronously, because we don't want to abruptly interrupt
    // the kernel's execution.  Instead, it is thrown at well-defined
    // points in the kernel: when the kernel blocks and when the kernel
    // calls process code.  When the ProcessStopException propagates
    // up to the process's part of the stack, the exception handling
    // skips over the process's stack frames and continues propagating
    // the ProcessStopException in the kernel.
    public class ProcessStopException : SystemException
    {
        public ProcessStopException() : base("Arg_ProcessStopException") {}
        public ProcessStopException(String message) : base(message) {}
        public ProcessStopException(String message, Exception inner) : base(message, inner) {}
    }
}

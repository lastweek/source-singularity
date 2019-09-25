//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Microsoft.Singularity 
{
    using System;
    using System.Runtime.CompilerServices;

    // If a process throws an exception to the kernel, the
    // exception handling mechanism throws a new ProcessUncaughtException
    // into the kernel's code.  This ensures that the kernel
    // does not see the process's exception object, which lives
    // in a different GC domain.
    [AccessedByRuntime("referenced from halforgc.asm")]
    public class ProcessUncaughtException : SystemException
    {
        public ProcessUncaughtException() : base("Arg_ProcessUncaughtException") {}
        public ProcessUncaughtException(String message) : base(message) {}
        public ProcessUncaughtException(String message, Exception inner) : base(message, inner) {}

        [AccessedByRuntime("referenced from halforgc.asm")]
        internal static unsafe void ThrowProcessUncaughtException()
        {
            ThreadContext *context = Processor.GetCurrentThreadContext();
            context->uncaughtFlag = false;
            throw new ProcessUncaughtException();
        }
    }
}

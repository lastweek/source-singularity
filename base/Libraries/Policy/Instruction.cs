// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace Microsoft.Singularity.Policy.Engine
{
    internal delegate void Execute();
    // An Instruction represents an abstract WAM instruction,
    // using a method delegate. All instructions have length 1.
    internal class Instruction {
        internal Execute _execute;
        internal Instruction(Execute execute) { _execute = execute; }
    }
}

// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

﻿
namespace Microsoft.Singularity.Policy.Engine
{
    // An Environment is a single Cell containing an environment. This replaces
    // the multiple cells used in the WAM in a more strongly typed way. The
    // Environment is followed on the stack by the permanent arguments.
    internal class Environment : Cell {
        internal readonly uint _n;
        internal readonly Address _ce;
        internal readonly Address _cp;
        internal Environment(uint n, Address ce, Address cp) {
            _n = n;
            _ce = ce;
            _cp = cp;
        }
        public override string ToString() {
            return "<ENVIRONMENT "
                 + _n.ToString()
                 + " "
                 + _ce.ToString()
                 + " "
                 + _cp.ToString()
                 + ">";
        }
    }
}

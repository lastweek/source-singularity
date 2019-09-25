///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

using System;

namespace Microsoft.Singularity.UnitTest
{
    // TODO
    //
    [AttributeUsage(AttributeTargets.Method, AllowMultiple = false)]
    public sealed class TestMethodAttribute : Attribute
    {
        //public TestMethodAttribute(string name) { }

        private long timeout;
        public long Timeout {
            get { return timeout; }
            set { timeout = value; }
        }
    }

}

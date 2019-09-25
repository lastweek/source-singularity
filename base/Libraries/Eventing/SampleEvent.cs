// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Transform;
using Microsoft.Singularity.Eventing;

namespace Microsoft.Singularity.EventTest
{
    [Event]
    public abstract class SampleSource : EventSource
    {
        [Event]
        public abstract bool One(int one, bool two, string three, int four);
        public static string One_Format = "One - {0} to {1} with {2} and {3}";

        [Event]
        public abstract bool Two(int a, int b, int c);
        public static string Two_Format; // leave default

        SampleSource(string sourceName, EventingStorage storage, uint controlFlags) 
            :base(sourceName, storage, controlFlags) {}
    }
}

////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ServiceRequest.cs
//
//  Note:
//

namespace Microsoft.Singularity
{
    public abstract class ServiceRequest
    {
        internal ServiceRequest next = null;
        protected internal abstract void Service();
    }
}

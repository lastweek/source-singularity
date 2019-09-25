///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Services\ServiceManager\AccessControlException.cs
//
//  Note:   Exception for service access control
//
using System;

namespace Microsoft.Singularity.Services.ServiceManager
{
    public class AccessControlException : Exception
    {
    }

    class InvalidStateException : Exception
    {
        public InvalidStateException()
            : base("Invalid state")
        {}
    }
}

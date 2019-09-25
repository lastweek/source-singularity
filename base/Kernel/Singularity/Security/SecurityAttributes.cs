///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DriverAttributes.cs
//
//  Warning:  This file is compiled into the kernel, and into the runtime.
//            In order to get the visibility correct in all cases, some #ifs
//            are needed
//
//  New Design:
//          This now conforms with the ideas presented in the Genesis papers,
//          chapter 3.  In particular, a device driver is simply a Category,
//          and anything that is in an app manifest is either intrinsic to
//          apps/installations (and hence not a decoration), or else a
//          PropertySet or Category.

using System;

namespace Microsoft.Singularity.Security
{

    //
    //  Application security specifiers
    //

    //////////////////////////////////////////////////////////////////////////
    //
    // ApplicationPublisherAttribute
    //
    // Purpose: Top-level metadata indicating the publisher name for an
    //          application.
    //
    [AttributeUsage(AttributeTargets.Assembly, AllowMultiple = false)]
    public class ApplicationPublisherAttribute : System.Attribute
    {
        private string publisher;

        public ApplicationPublisherAttribute(string _publisher)
        {
            this.publisher = _publisher;
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // AssertPrivilegeAttribute
    //
    // Purpose: Top-level metadata indicating that the publisher asserts that
    // application is a member of the argument group
    //
    [AttributeUsage(AttributeTargets.Assembly, AllowMultiple = true)]
    public class AssertPrivilegeAttribute : System.Attribute
    {
        private string privilege;

        public AssertPrivilegeAttribute(string _privilege)
        {
            this.privilege = _privilege;
        }
    }
}

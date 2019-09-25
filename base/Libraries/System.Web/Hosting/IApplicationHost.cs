//------------------------------------------------------------------------------
// <copyright file="ApplicationManager.cs" company="Microsoft">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//------------------------------------------------------------------------------

namespace System.Web.Hosting
{
    using System;
    using System.Collections;
    using System.Web;

    public interface IApplicationHost {
        String GetVirtualPath();
        String GetPhysicalPath();
        //IConfigMapPathFactory GetConfigMapPathFactory();
        IntPtr GetConfigToken();
        String GetSiteName();
        void MessageReceived();
        bool IsHostProcessMultiInstance();
    }
}

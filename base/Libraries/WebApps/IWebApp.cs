///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   The interface implemented by web applications under Singularity
//

//
// This interface is the base class for web applications, whether or not
// they are run in-process or out-of-process.
//
namespace Microsoft.Singularity.WebApps
{
    public interface IWebApp
    {
        void ProcessRequest(IHttpRequest! request);
    }
}

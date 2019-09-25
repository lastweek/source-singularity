///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   The interface implemented by Http request objects, as processed by
//          web applications under Singularity.
//

using Microsoft.SingSharp;
using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

namespace Microsoft.Singularity.WebApps
{
    public interface IHttpRequest
    {
        // Methods to fetch information about the request
        string! GetUriPath();
        string GetQueryString();
        string GetVerb();
        string GetHeader(string! headerName);
        byte[] GetBodyData();
        string! GetRemoteAddress();

        // Methods to push response data
        void SendStatus(int code, string! description);
        void SendHeader(string! name, string! value);
        void SendBodyData(byte[]! data);
        void SendBodyData([Claims] byte[]! in ExHeap data);

        // Call this once when done processing
        void Done();
    }
}

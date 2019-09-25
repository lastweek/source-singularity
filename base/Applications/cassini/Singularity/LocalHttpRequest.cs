///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    This file wraps a cassini Request object so it is callable through
//    the Microsoft.Singularity.WebApps.IHttpRequest interface that web
//    applications understand.
//    regular object.
//

using System;
using Microsoft.SingSharp;
using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.WebApps;
using System.Web;
using System.Threading;

namespace Microsoft.VisualStudio.WebHost
{
    internal class LocalHttpRequest : IHttpRequest
    {
        private Request m_Req;
        private byte[] cachedBodyData = null;
        private Mutex bodyDataMutex = new Mutex();

        internal LocalHttpRequest(Request request)
        {
            m_Req = request;
        }

        public string! GetUriPath()
        { return (!)m_Req.GetUriPath(); }

        public string GetQueryString()
        { return m_Req.GetQueryString(); }

        public string GetVerb()
        { return m_Req.GetHttpVerbName(); }

        public string GetHeader(string! headerName)
        {
            int knownIndex = HttpWorkerRequest.GetKnownRequestHeaderIndex(headerName);

            if (knownIndex > 0) {
                return m_Req.GetKnownRequestHeader(knownIndex);
            }
            else {
                return m_Req.GetUnknownRequestHeader(headerName);
            }
        }

        public string! GetRemoteAddress()
        { return m_Req.GetRemoteAddress(); }

        // Caller should not modify this buffer!
        public byte[] GetBodyData()
        {
            if (m_Req.IsEntireEntityBodyIsPreloaded()) {
                // Return a copy of the preloaded body and trust the
                // caller not to monkey with it.
                return m_Req.GetPreloadedEntityBody();
            }
            else {

                int totalBodyLength = m_Req.GetTotalEntityBodyLength();

                if (totalBodyLength == 0) {
                    return null; // No body expected at all
                }
                // Else there is body data that wasn't received as part of
                // the initial request.

                if (cachedBodyData == null) {
                    try {
                        bodyDataMutex.AcquireMutex();

                        if (cachedBodyData != null) {
                            // Someone loaded this concurrently to us
                            return cachedBodyData;
                        }

                        byte[] preloadedBody = m_Req.GetPreloadedEntityBody();
                        int preloadedLength = m_Req.GetPreloadedEntityBodyLength();
                        byte[] body = new byte[totalBodyLength];

                        if ((preloadedLength > 0) && (preloadedBody != null)) {
                            // First copy the cached portion
                            Buffer.BlockCopy(preloadedBody, 0,
                                             body, 0, preloadedLength);
                        }
                        else {
                            assert ((preloadedBody == null) && (preloadedLength == 0));
                        }

                        // Now read in any remainder
                        int remainder = totalBodyLength - preloadedLength;
                        assert remainder > 0; // Tested earlier

                        while (remainder > 0) {
                            int readBytes = m_Req.ReadEntityBody(body, totalBodyLength - remainder,
                                                                 remainder);

                            if (readBytes == 0) {
                                // Body wasn't as long as we were expecting for some
                                // reason! This could be because the remote client
                                // lied to us in the headers. Truncate the cached
                                // data to the actual body size.
                                byte[] shortBody = new byte[totalBodyLength - remainder];
                                Array.Copy(body, 0, shortBody, 0, totalBodyLength - remainder);
                                body = shortBody;
                                remainder = 0; // No more data will be forthcoming
                            }
                            else {
                                remainder -= readBytes;
                            }
                        }

                        // Stash this for other callers
                        cachedBodyData = body;
                    }
                    finally {
                        bodyDataMutex.ReleaseMutex();
                    }
                }
                // else we previously cached the body data.

                return cachedBodyData;
            }
        }

        public void SendStatus(int code, string! description)
        { m_Req.SendStatus(code, description); }

        public void SendHeader(string! name, string! value)
        {
            int index = HttpWorkerRequest.GetKnownResponseHeaderIndex(name);

            if (index == -1) {
                m_Req.SendUnknownResponseHeader(name, value);
            }
            else {
                m_Req.SendKnownResponseHeader(index, value);
            }
        }

        public void SendBodyData(byte[]! data)
        {
            m_Req.SendResponseFromMemory(data, data.Length);
            m_Req.FlushResponse(false); // always transmit immediately
        }

        public void SendBodyData([Claims] byte[]! in ExHeap data)
        {
            m_Req.SendResponseFromMemory(data);
            m_Req.FlushResponse(false); // always transmit immediately
        }

        public void Done()
        {
            m_Req.FlushResponse(true);
            m_Req.EndOfRequest();
        }
    }
}

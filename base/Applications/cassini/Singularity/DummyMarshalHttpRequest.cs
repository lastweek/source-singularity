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
//
//    As an added twist, this object simulates the data marshalling that
//    is normally required to use channels.
//

using System;
using Microsoft.SingSharp;
using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.WebApps;
using System.Web;

namespace Microsoft.VisualStudio.WebHost
{
    internal class DummyMarshallHttpRequest : IHttpRequest
    {
        private Request m_Req;
        public ulong m_TotalSharedAllocTime;
        public ulong m_TotalSharedCharCopyTime;
        public ulong m_TotalSharedByteCopyTime;
        public ulong m_TotalNativeTime;
        public ulong m_TotalSharedDeleteTime;

        internal DummyMarshallHttpRequest(Request request)
        {
            m_Req = request;
            m_TotalSharedAllocTime = 0;
            m_TotalSharedCharCopyTime = 0;
            m_TotalSharedCharCopyTime = 0;
            m_TotalNativeTime = 0;
            m_TotalSharedDeleteTime = 0;
        }

        private string! MarshallString(string str)
        {
            if (str == null) return "";

            ulong start = Processor.CycleCount;
            char[] in ExHeap marshalled = new[ExHeap] char[str.Length];
            m_TotalSharedAllocTime += Processor.CycleCount - start;

            start = Processor.CycleCount;
            int length = str.Length;
            for (int i = 0; i < length; ++i) {
                marshalled[i] = str[i];
            }
            m_TotalSharedCharCopyTime += Processor.CycleCount - start;

            start = Processor.CycleCount;
            string reborn = Bitter.ToString2(marshalled);
            m_TotalNativeTime += Processor.CycleCount - start;

            start = Processor.CycleCount;
            delete marshalled;
            m_TotalSharedDeleteTime += Processor.CycleCount - start;

            return reborn;
        }

        private byte[]! MarshallBytes(byte[]! bytes)
        {
            ulong start = Processor.CycleCount;
            byte* opt(ExHeap[]) marshalled = new[ExHeap] byte[bytes.Length];
            m_TotalSharedAllocTime += Processor.CycleCount - start;

            start = Processor.CycleCount;
            int length = bytes.Length;
            for (int i = 0; i < length; ++i) {
                marshalled[i] = bytes[i];
            }
            m_TotalSharedByteCopyTime += Processor.CycleCount - start;

            start = Processor.CycleCount;
            byte[] reborn = Bitter.ToByteArray(marshalled);
            m_TotalNativeTime += Processor.CycleCount - start;

            start = Processor.CycleCount;
            delete marshalled;
            m_TotalSharedDeleteTime += Processor.CycleCount - start;

            return reborn;
        }

        public string! GetUriPath()
        { return MarshallString(m_Req.GetUriPath()); }

        public string GetQueryString()
        { return MarshallString(m_Req.GetQueryString()); }

        public string GetVerb()
        { return MarshallString(m_Req.GetHttpVerbName()); }

        public string! GetRemoteAddress()
        { return MarshallString(m_Req.GetRemoteAddress()); }

        public byte[] GetBodyData()
        { return MarshallBytes(m_Req.GetPreloadedEntityBody()); }

        public string GetHeader(string! headerName)
        {
            int knownIndex = HttpWorkerRequest.GetKnownRequestHeaderIndex(headerName);

            if (knownIndex > 0) {
                return MarshallString(m_Req.GetKnownRequestHeader(knownIndex));
            }
            else {
                return MarshallString(m_Req.GetUnknownRequestHeader(headerName));
            }
        }

        public void SendStatus(int code, string! description)
        { m_Req.SendStatus(code, MarshallString(description)); }

        public void SendHeader(string! name, string! value)
        {
            int index = HttpWorkerRequest.GetKnownResponseHeaderIndex(name);

            name = MarshallString(name);
            value = MarshallString(value);

            if (index == -1) {
                m_Req.SendUnknownResponseHeader(name, value);
            }
            else {
                m_Req.SendKnownResponseHeader(index, value);
            }
        }

        public void SendBodyData(byte[]! data)
        {
            byte[] reborn = MarshallBytes(data);
            m_Req.SendResponseFromMemory(reborn, reborn.Length);
        }

        public void SendBodyData([Claims] byte[]! in ExHeap data)
        {
            m_Req.SendResponseFromMemory(Bitter.ToByteArray(data), data.Length);
            delete data;
        }

        public void Done()
        {
            m_Req.FlushResponse(true);
            m_Req.EndOfRequest();
        }
    }
}

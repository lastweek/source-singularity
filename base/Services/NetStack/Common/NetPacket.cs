// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

using System.Collections;
using System.Diagnostics;
using System;
using System.Compiler;

using Drivers.Net;

namespace NetStack.Common
{
    public class NetPacket : SimpleBuffer
    {
        public const int DefaultSize = 1514;

        private static uint lastId;

        private uint id;

        // an overlapped context
        protected object overlapContext;

        // a target/source adapter context
        protected object adapterContext;

        protected object mux;

        // the following are only used for Qos extension
        protected object sessionContext;

        // some ctors
        public NetPacket(byte[]! buffer, int index, int count)
            : base(buffer, index, count)
        {
            id = lastId++;
        }

        public NetPacket(byte[]! buffer) : base(buffer)
        {
            id = lastId++;
        }

        public NetPacket(int capacity) : base(capacity)
        {
            id = lastId++;
        }

        public NetPacket() : base(DefaultSize)
        {
            id = lastId++;
        }

        public uint Id { get { return id; } }

        public object SessionContext
        {
            get { return sessionContext;  }
            set { sessionContext = value; }
        }

        // get/set the context (IPHeader, cryptically enough!)
        public object OverlapContext
        {
            get { return overlapContext; }
            set { overlapContext=value; }
        }

        // get/set the context
        public object AdapterContext
        {
            get { return adapterContext; }
            set { adapterContext = value; }
        }

        // get/set the Multiplexer
        public object Mux
        {
            get { return mux; }
            set { mux = value; }
        }

        /// <summary>
        /// should only copy the data from position to count
        /// </summary>
        public byte[] ToUser()
        {
            // Much to do here
            byte[] toUser = new byte[Available];
            Array.Copy(this.data, this.position, toUser, 0, Available);
            return toUser;
        }

        public byte[] ToContiguous()
        {
            byte [] contiguous = new byte [this.Length];
            Array.Copy(this.data, 0, contiguous, 0, this.Length);
            return contiguous;
        }

        public bool IsOneChunk
        {
            get { return true; }
        }

        /// <summary>
        /// Clips the remaining bytes (after the current position)
        /// </summary>
        /// <param name="remaining"></param>
        public void Clip(int remaining)
        {
            this.count = this.position + remaining + 1;
        }

        /// <summary>
        /// Clips the bytes outside the window
        /// remaining counts the bytes after the headIndex
        /// </summary>
        public void Clip(int headIndex,int remaining)
        {
            Debug.Assert(this.count > headIndex + remaining);
            this.position = headIndex;
            this.count    = this.position + remaining + 1;
        }

        // reset the packet to the original clipping
        public void Reset()
        {
            this.position       = 0;
            this.sessionContext = null;
            this.overlapContext = null;
            this.mux = null;
            this.adapterContext = null;
        }

        public void Reset(int newLength)
        {
            Reset();
            this.count = newLength;
        }

        public byte [] GetRawData()
        {
            return this.data;
        }
    } // class NetPacket
} // namespace Drivers.Net

////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TcpVectorQueue.sg
//
//  Note: This is a modified version of the VectorQueue found
//        in the Sing# runtime.  It's tailored specifically for TCP,
//        allowing shared heap segments to be trimmed without copies
//        or reallocations. This is especially useful for reassembly

//#define DEBUG_TCPVECTORQ

using System;
using System.Collections;
using System.Diagnostics;

using Microsoft.Singularity;
using Microsoft.SingSharp;
using Microsoft.Singularity.Channels;
using MonitorLock = System.Threading.MonitorLock;

namespace Microsoft.Singularity.NetStack2
{
    public class TContainerVectorQueueByte
    {
        MonitorLock thisLock = new MonitorLock();
        VectorQueueByte o;

        public TContainerVectorQueueByte(VectorQueueByte o) {
            VTable.Assert(o != null);
            this.o = o;
        }

        public VectorQueueByte Acquire() {
            thisLock.Acquire();
            return o;
        }

        public void Release(VectorQueueByte v) {
            o = v;
            thisLock.Release();
        }
    }

    public class TContainerTcpVectorQueueByte
    {
        MonitorLock thisLock = new MonitorLock();
        TcpVectorQueueByte o;

        public TContainerTcpVectorQueueByte(TcpVectorQueueByte o) {
            VTable.Assert(o != null);
            this.o = o;
        }

        public TcpVectorQueueByte Acquire() {
            thisLock.Acquire();
            return o;
        }

        public void Release(TcpVectorQueueByte v) {
            o = v;
            thisLock.Release();
        }
    }

    public class VectorQueueByte
    {
        [Conditional("DEBUG_TCPVECTORQ")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("TCPVECTORQ: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        [Conditional("DEBUG_TCPVECTORQ")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print("TCPVECTORQ: {0}",
                            DebugStub.ArgList(format));
        }

        private VectorNode listHead;
        private VectorNode listTail;
        private uint  size;  //size of data in queue in bytes
        private int   count; //number of elements

        private VectorNode currentTxBuff;
        private uint currentTxBufferOffset;
        private uint currentTxTotalOffset;

        public VectorQueueByte() {
            size = 0;
            count = 0;
            VectorNode node = this.listHead = new VectorNode();
            this.listTail = node;
            currentTxBuff = null;
            currentTxBufferOffset = 0;
            currentTxTotalOffset = 0;
        }

        public class VectorNode {
            internal Bytes data;

//            public uint startOffset; //where useful (for TCP reassembly) data begins
//            public uint length;      //useful length

            internal VectorNode next;
            internal VectorNode prev;

            internal VectorNode() {
                this.next = this;
                this.prev = this;
            }

            internal VectorNode(Bytes arg) {
                this.next = this;
                this.prev = this;
                this.data = arg;
            }
/*
            internal VectorNode(Bytes arg, uint length) {
                this.next = this;
                this.prev = this;
                this.data = arg;
                this.startOffset = 0;
                this.length = length;
            }
*/

            internal Bytes Unlink() {
                this.prev.next = this.next;
                this.next.prev = this.prev;
                this.next = this;
                this.prev = this;
                return this.data;

            }

            internal VectorNode BoxedUnlink() {
                this.prev.next = this.next;
                this.next.prev = this.prev;
                this.next = this;
                this.prev = this;
                return this;
            }

            internal void LinkAsNext(VectorNode tcpVNode)
            {
                tcpVNode.next = this.next;
                this.next = tcpVNode;
                tcpVNode.prev = this;
                tcpVNode.next.prev = tcpVNode;
            }

/*
            internal void LinkAsNext(Bytes data, uint length) {
                VectorNode next = new VectorNode(data, length);
                next.next = this.next;
                this.next = next;
                next.prev = this;
                next.next.prev = next;
            }
*/

            internal void LinkAsPrev(VectorNode tcpVNode)
            {
                tcpVNode.prev = this.prev;
                this.prev = tcpVNode;
                tcpVNode.next = this;
                tcpVNode.prev.next = tcpVNode;
            }

/*
            internal void LinkAsPrev(Bytes data, uint length) {
                VectorNode prev = new VectorNode(data, length);
                prev.prev = this.prev;
                this.prev = prev;
                prev.next = this;
                prev.prev.next = prev;
            }

            internal void TrimStart(uint bytes)
                //requires bytes >= 0;
                //requires data != null;
                //requires bytes < this.length;
            {
                this.startOffset += bytes;
                this.length -= bytes;
            }

            internal void TrimEnd(uint bytes)
                //requires bytes >= 0;
                //requires bytes < (this.length - this.startOffset);
            {
                this.length -= bytes;
            }
*/
        }

//        public void Release() {}
//        public void Acquire() {}
        public void Dispose()
        {
            VectorNode current = this.listHead.next;
            while (current != this.listHead) {
                // temporary hack until we fix the upcast in receiver context
                    Bytes data = current.data;
                    if (data != null) {
                        //delete data;
                    }
                current = current.next;
            }
            this.listTail = this.listHead = new VectorNode();
        }

        //only useful if the queue is storing Bytes
        public uint Size()
        {
            return size;
        }

        public int Count()
        {
            VTable.Assert(count >=0);
            return count;
        }

        public void AddHead(VectorNode tcpVNode)
        {
            this.size += (uint)tcpVNode.data.Length;
            this.count++;
            this.listHead.LinkAsNext(tcpVNode);
        }

/*
        public void AddHead(Bytes data, uint length) {

            this.size += length;
            this.count++;
            this.listHead.LinkAsNext(data, length);
        }
*/

        public void AddHead(Bytes data) {
//            AddHead(data, (uint) data.Length);
            this.size += (uint)data.Length;
            this.count++;
            this.listHead.LinkAsNext(new VectorNode(data));
        }

        public void AddTail(VectorNode tcpVNode)
        {
            this.size += (uint)tcpVNode.data.Length;
            this.count++;
            this.listTail.LinkAsPrev(tcpVNode);
        }

/*
        public void AddTail(Bytes data, uint length) {
            size += length;
            this.count++;
            this.listTail.LinkAsPrev(data, length);
        }
*/

        public void AddTail(Bytes data) {
            DebugStub.Assert(data.Length != 0);
//            AddTail(data, (uint) data.Length);
            size += (uint)data.Length;
            this.count++;
            this.listTail.LinkAsPrev(new VectorNode(data));
        }

        public bool Empty { get { return this.listHead.next == this.listTail; } }

        public Bytes ExtractHead()
        {
            if (this.Empty) return null;

            VectorNode candidate = this.listHead.next;
            //VTable.Assert(candidate.length != 0);
            size -= (uint)candidate.data.Length;
            count--;
            return candidate.BoxedUnlink().data;
        }
    }

    public class TcpVectorQueueByte
    {
        [Conditional("DEBUG_TCPVECTORQ")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("TCPVECTORQ: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        [Conditional("DEBUG_TCPVECTORQ")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print("TCPVECTORQ: {0}",
                            DebugStub.ArgList(format));
        }

        private TcpVectorNode listHead;
        private TcpVectorNode listTail;
        private uint  size;  //size of data in queue in bytes
        private int   count; //number of elements

        private TcpVectorNode currentTxBuff;
        private uint currentTxBufferOffset;
        private uint currentTxTotalOffset;

        public TcpVectorQueueByte() {
            size = 0;
            count = 0;
            TcpVectorNode node = this.listHead = new TcpVectorNode();
            this.listTail = node;
            currentTxBuff = null;
            currentTxBufferOffset = 0;
            currentTxTotalOffset = 0;
        }

        public class TcpVectorNode {
            internal Bytes data;

            public uint seqNumber;   //seqnumber where this data begins
            public uint startOffset; //where useful (for TCP reassembly) data begins
            public uint length;      //useful length

            internal TcpVectorNode next;
            internal TcpVectorNode prev;

            internal TcpVectorNode() {
                this.next = this;
                this.prev = this;
            }

            internal TcpVectorNode(Bytes arg, uint seqNumber, uint length) {
                this.next = this;
                this.prev = this;
                this.data = arg;
                this.seqNumber = seqNumber;
                this.startOffset = 0;
                this.length = length;
            }

            internal Bytes Unlink() {
                this.prev.next = this.next;
                this.next.prev = this.prev;
                this.next = this;
                this.prev = this;
                return this.data;

            }

            internal TcpVectorNode BoxedUnlink() {
                this.prev.next = this.next;
                this.next.prev = this.prev;
                this.next = this;
                this.prev = this;
                return this;
            }

            internal void LinkAsNext(TcpVectorNode tcpVNode)
            {
                tcpVNode.next = this.next;
                this.next = tcpVNode;
                tcpVNode.prev = this;
                tcpVNode.next.prev = tcpVNode;
            }

            internal void LinkAsNext(Bytes data, uint seqNumber, uint length) {
                TcpVectorNode next = new TcpVectorNode(data, seqNumber, length);
                next.next = this.next;
                this.next = next;
                next.prev = this;
                next.next.prev = next;
            }

            internal void LinkAsPrev(TcpVectorNode tcpVNode)
            {
                tcpVNode.prev = this.prev;
                this.prev = tcpVNode;
                tcpVNode.next = this;
                tcpVNode.prev.next = tcpVNode;
            }

            internal void LinkAsPrev(Bytes data, uint seqNumber, uint length) {
                TcpVectorNode prev = new TcpVectorNode(data, seqNumber, length);
                prev.prev = this.prev;
                this.prev = prev;
                prev.next = this;
                prev.prev.next = prev;
            }

            internal void TrimStart(uint bytes)
                //requires bytes >= 0;
                //requires data != null;
                //requires bytes < this.length;
            {
                this.startOffset += bytes;
                this.length -= bytes;
            }

            internal void TrimEnd(uint bytes)
                //requires bytes >= 0;
                //requires bytes < (this.length - this.startOffset);
            {
                this.length -= bytes;
            }

        }

//        public void Release() {}
//        public void Acquire() {}
        public void Dispose()
        {
            TcpVectorNode current = this.listHead.next;
            while (current != this.listHead) {
                // temporary hack until we fix the upcast in receiver context
                    Bytes data = current.data;
                    if (data != null) {
                        //delete data;
                    }
                current = current.next;
            }
            this.listTail = this.listHead = new TcpVectorNode();
        }

        //only useful if the queue is storing Bytes
        public uint Size()
        {
            return size;
        }

        public int Count()
        {
            VTable.Assert(count >=0);
            return count;
        }

        public void AddHead(TcpVectorNode tcpVNode)
        {
            this.size += tcpVNode.length;
            this.count++;
            this.listHead.LinkAsNext(tcpVNode);
        }

        public void AddHead(Bytes data, uint seqNumber, uint length) {

            this.size += length;
            this.count++;
            this.listHead.LinkAsNext(data, seqNumber, length);
        }


        public void AddHead(Bytes data, uint seqNumber) {
            AddHead(data, seqNumber, (uint) data.Length);
        }

        public void AddTail(TcpVectorNode tcpVNode)
        {
            this.size += tcpVNode.length;
            this.count++;
            this.listTail.LinkAsPrev(tcpVNode);
        }

        public void AddTail(Bytes data, uint seqNumber, uint length) {
            size += length;
            this.count++;
            this.listTail.LinkAsPrev(data, seqNumber, length);
        }

        public void AddTail(Bytes data, uint seqNumber) {
            DebugStub.Assert(data.Length != 0);
            AddTail(data, seqNumber, (uint) data.Length);
        }

        public TcpVectorNode PopNextContiguousSegment(uint targetSeqNumber,
                                                      uint windowSize)
        {
            if (this.listHead == this.listTail) {
                return null;
            }

            TcpVectorNode candidate = this.listHead.next;
            VTable.Assert(candidate.data != null);

            if (candidate.length > windowSize) {
                DebugPrint("Window full, can't pop waiting segment\n");
                return null;
            }
            if (candidate.seqNumber == targetSeqNumber) {
                return this.ExtractHead();
            }
            DebugPrint("PopNextContiguousSegment: None available.  target seq number {0} head of list seq number {1}\n",
                       targetSeqNumber, candidate.seqNumber);
            return null;
        }

        public bool ReleaseDataFromTxBuffer(uint bytes)
        {
            uint totalBytes = bytes;

            if (this.Empty) {
                DebugStub.Print ("Attempting to release {0} bytes on an empty list? size {1}\n",
                                 DebugStub.ArgList(bytes, this.size));
                DebugStub.Break();
                return false;
            }
            else if (bytes > this.size) {
                DebugStub.Print("Ack! attempting to release {0} bytes size {1} bytes\n", DebugStub.ArgList(bytes, this.size));
                bytes = this.size;
            }
            if (bytes > this.currentTxTotalOffset) {
                DebugStub.Print("ack! trying to release more than total offset??\n");
                DebugStub.Break();
            }

            TcpVectorNode candidate = this.listHead.next;
            while (bytes != 0) {
                if (candidate.length <= bytes) {
                    TcpVectorNode toFree = candidate;
                    candidate = candidate.next;
                    bytes = bytes - toFree.length;
                    this.size -= toFree.length;
                    if (this.currentTxBuff == toFree) {
                        this.currentTxBuff = null;
                        this.currentTxBufferOffset = 0;
                    }
                    Bytes data = toFree.Unlink();
                    this.count--;
                    if (data != null) {
                        //delete data;
                    }
                }
                else {
                    candidate.TrimStart(bytes);
                    //this happens when some packets being retransmitted are
                    //acknowledged during retransmission.
                    if ((candidate == this.currentTxBuff) &&
                        (candidate.startOffset > this.currentTxBufferOffset)) {
                        DebugStub.WriteLine("startoffset was {0} now {1} current offset {2} totalBytes to Free {3}\n",
                                            DebugStub.ArgList((candidate.startOffset - bytes), candidate.startOffset,
                                                      this.currentTxBufferOffset, totalBytes));
                        this.currentTxBufferOffset = candidate.startOffset;
                    }

                    this.size -= bytes;
                    bytes = 0;
                }
            }
            if (this.Empty) {
                return false;
            }
            return true;
        }


        public Bytes GetCurrentBuffer(out int start,
                                              out int length,
                                              out int bufferOffset,
                                              int totalOffset)
        {
            DebugPrint("GetCurrentBuffer: totalOffset{0} currentTxTotalOffset {1} currentTxBufferOffset {2}\n",
                       totalOffset, currentTxTotalOffset, currentTxBufferOffset);

            if (this.currentTxBuff != null && totalOffset == this.currentTxTotalOffset) {
                DebugPrint("GetCurrentBuff: fast path \n");
                start = (int) this.currentTxBuff.startOffset;
                length = (int) this.currentTxBuff.length;
                bufferOffset = (int) this.currentTxBufferOffset;
                return this.currentTxBuff.data;
            }
            DebugPrint("GetCurrentBuff...slowpath\n");
            TcpVectorNode candidate = this.listHead.next;

            uint amt = (uint) totalOffset;

            if (amt == 0) {
                this.currentTxBuff = this.listHead.next;
                this.currentTxTotalOffset = 0;
                this.currentTxBufferOffset = this.currentTxBuff.startOffset;
                start = (int) this.currentTxBuff.startOffset;
                length = (int) this.currentTxBuff.length;
                bufferOffset = (int) this.currentTxBuff.startOffset;

                return this.currentTxBuff.data;
            }

            while (amt > 0) {
                if (amt >  candidate.length) {
                    amt -=  candidate.length;
                    VTable.Assert(candidate.next != this.listTail);
                    candidate = candidate.next;
                    DebugStub.Assert(amt > 0);
                }
                else if (amt ==  candidate.length) {
                    DebugStub.Assert(amt >= 0);
                    amt -= candidate.length;
                    DebugStub.Assert(candidate.next != this.listTail);
                    VTable.Assert(candidate.next != this.listTail);
                    candidate = candidate.next;
                    start = (int) candidate.startOffset;
                    length = (int) candidate.length;
                    bufferOffset = (int) candidate.startOffset;
                    this.currentTxBuff = candidate;
                    this.currentTxTotalOffset = (uint) totalOffset;
                    this.currentTxBufferOffset = candidate.startOffset;
                    return candidate.data;
                }
                else {
                    DebugStub.Assert(amt >= 0);
                    bufferOffset = (int) (amt + candidate.startOffset);
                    start = (int) candidate.startOffset;
                    length = (int) candidate.length;
                    this.currentTxBuff = candidate;
                    this.currentTxTotalOffset = (uint) totalOffset;
                    this.currentTxBufferOffset = amt + candidate.startOffset;
                    return candidate.data;
                }
            }
            DebugStub.Print("ack! no buffer found!!!!\n");
            start = -1;
            length = -1;
            bufferOffset = -1;
            DebugStub.Assert(false);
            return null;
        }

        public Bytes GetNextBuffer(out int start, out int length)
        {
            if (this.Empty) {
                start = -1;
                length = -1;
                return null;
            }

            if (this.currentTxBuff == null) {
                this.currentTxBuff = this.listHead.next;
                this.currentTxTotalOffset = 0;
                this.currentTxBufferOffset = this.currentTxBuff.startOffset;
            }
            else {
                this.currentTxBuff = this.currentTxBuff.next;
                this.currentTxBufferOffset = this.currentTxBuff.startOffset;
                if (this.currentTxBuff == this.listTail) {
                    DebugStub.Print("GetBuffer: Empty list???\n");
                    DebugStub.Break();
                    start = -1;
                    length = -1;
                    return null;
                }
            }
            start = (int) this.currentTxBuff.startOffset;
            length = (int) this.currentTxBuff.length;

            return this.currentTxBuff.data;
        }

        public void AdvanceBufferOffset(uint newOffset)
        {
            DebugPrint("updating txbufferoffset {0}\n", newOffset);
            this.currentTxBufferOffset += newOffset;
        }

        public void SetTxBuffTotalOffset(uint newOffset)
        {
            DebugPrint("updating txtotaloffset {0}\n", newOffset);
            this.currentTxTotalOffset = newOffset;
        }


        public void AddInSeqOrder(Bytes data, uint seqNumber)
        {
            AddInSeqOrder(data, seqNumber, (uint) data.Length);
        }

        public void AddInSeqOrder(Bytes data, uint seqNumber, uint length)
        {
            if (this.Empty) {
                this.AddHead(data, seqNumber);
                return;
            }
            TcpVectorNode current = this.listHead.next;
            TcpVectorNode prev = null;
            while(current != this.listHead) {
                //see if we belong past the current node
                if (TcpHeader.SeqGreater(seqNumber, (current.seqNumber + current.length))) {
                    if (current.next == this.listHead.next) {
                        AddTail(data, seqNumber);
                        break;
                    }
                    prev = current;
                    current = current.next;
                    continue;
                }
                //so now we're either
                //a) independent of both the prev and next node (simple insertion)
                //b) overlap with part of the prev or next node (trim the buffer)
                //c) subsumed by packets already in the assembly queue (discard the packer)

                //subsumed by next segment
                if (TcpHeader.SeqGreater(seqNumber, current.seqNumber) &&
                    TcpHeader.SeqLess(seqNumber + length, current.seqNumber + current.length)) {
                    DebugPrint("data completely subsumed by existing segment\n");
                    //delete data;
                    break;
                }
                //subsumed by prev segment
                if (prev != null &&
                    TcpHeader.SeqGEQ(seqNumber, prev.seqNumber) &&
                    TcpHeader.SeqLEQ(seqNumber + length, prev.seqNumber + prev.length)) {
                    DebugPrint("data completely subsumed by existing segment\n");
                    //delete data;
                    break;
                }
                //subsumed because next and prev are contiguous
                if (prev != null &&
                    TcpHeader.SeqEQ(prev.seqNumber + length, current.seqNumber)) {
                    DebugPrint("data completely subsumed by existing segment\n");
                    //delete data;
                    break;
                }
                //a)
                if (TcpHeader.SeqLess(seqNumber, current.seqNumber) &&
                    TcpHeader.SeqLEQ(seqNumber + length, current.seqNumber) &&
                    ((prev == null) || TcpHeader.SeqGEQ(seqNumber, (prev.seqNumber + prev.length)))) {
                    DebugPrint("new segment fits between two existing segments\n");
                    current.LinkAsPrev(data, seqNumber, length);
                    break;
                }
                //b)
                int trimEnd = 0;
                if  (TcpHeader.SeqLess(seqNumber, current.seqNumber)  &&
                     TcpHeader.SeqGreater(seqNumber + length, current.seqNumber)) {
                    //we could worry about this segment subsuming later segments...
                    //instead we trim to fit (since we aleady have the later data
                    trimEnd = (int) length - (int) (current.seqNumber - seqNumber);
                    DebugStub.Assert(trimEnd > 0);
                }
                if (prev == null) {
                    DebugStub.Assert(trimEnd > 0);
                    current.LinkAsPrev(data, seqNumber, length);
                    current.prev.TrimEnd( (uint) trimEnd);
                    break;
                }
                int trimStart = 0;
                if (TcpHeader.SeqLess(seqNumber, prev.seqNumber + prev.length)) {
                    //at this point we know there is some gap between prev and next
                    trimStart = (int) ((prev.seqNumber + prev.length) - seqNumber);
                    DebugStub.Assert(trimStart > 0);
                    VTable.Assert(trimStart > 0);
                }
                current.LinkAsPrev(data, seqNumber, length);
                current.prev.TrimStart((uint) trimStart);
                current.prev.TrimEnd((uint) trimEnd);
                break;
            }

        }

        public bool Empty { get { return this.listHead.next == this.listTail; } }


        public Bytes ExtractHead(out uint startOffset, out uint length) {
            if (this.Empty) {
                startOffset = 0;
                length = 0;
                return null;
            }
            TcpVectorNode candidate = this.listHead.next;
            Bytes data = candidate.Unlink();
            count--;
            if (data != null) {
                size -= candidate.length;
            }
            else {
                DebugStub.WriteLine("Extracthead no data??\n");
                DebugStub.Break();
                VTable.Assert(false);
            }
            startOffset = candidate.startOffset;
            length = candidate.length;
            return data;
        }

        public TcpVectorNode ExtractHead()
        {
            if (this.Empty) return null;

            TcpVectorNode candidate = this.listHead.next;
            VTable.Assert(candidate.length != 0);
            size -= candidate.length;
            count--;
            return candidate.BoxedUnlink();
        }

        public Bytes ExtractTail(out uint startOffset, out uint length) {
            if (this.Empty) {
                startOffset = 0;
                length = 0;
                return null;
            }
            TcpVectorNode candidate = this.listTail.prev;

            Bytes data = candidate.Unlink();
            count--;
            if (data != null) {
                size -= candidate.length;
            }
            startOffset = candidate.startOffset;
            length = candidate.length;
            return data;
        }
    }
}

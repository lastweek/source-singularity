////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    A utility class that can store vectors of bytes from the shared heap without
//    duplicating them, then copy them out later as though they were a single
//    uninterrupted array of bytes.
//

//using Microsoft.SingSharp;
//using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using System.Collections;
//using System.Collections.Generic;
using System.Diagnostics;

namespace System.Net.Sockets
{
    internal class TrackedBytesBuffer
    {
        private class BytesPlusCount
        {
            int nextOffset; // Offset of the next byte to use
            Bytes bytes; // The bytes

            public BytesPlusCount(Bytes data)
            {
                bytes = data;
                nextOffset = 0;
            }

            #region ITracked members

            //void ITracked.Release() {}
            //void ITracked.Acquire() {}

            public void Dispose()
            {
                //delete bytes;
            }

            //void ITracked.Expose() {}
            //void ITracked.UnExpose() {}

            #endregion

            public int Length
            {
                get {
                        return bytes.Length - nextOffset;
                }
            }

            public bool Empty
            {
                get {
                        return nextOffset >= bytes.Length;
                }
            }

            // Copy out as many bytes as possible
            public int CopyOut(byte[] buff, int offset, int length, bool fPeek)
            {
                if (Length <= 0) {
                    return 0;
                }

                int numToCopy = Math.Min(length, Length);

                {
                    for (int i = 0; i < numToCopy; ++i) {
                        buff[offset + i] = bytes[nextOffset + i];
                    }
                }

                if (!fPeek) {
                    nextOffset += numToCopy;
                }
                // else it's as if the copy never happened

                return numToCopy;
            }
        }

        // Contains TRef<BytesPlusCount>
        private Queue m_DataQueue;

        // Count of the total bytes that we (logically) contain
        private int m_Count;

        public TrackedBytesBuffer()
        {
            m_DataQueue = new Queue();
            m_Count = 0;
        }

        public void AddToTail(Bytes bytes)
        {
            m_Count += bytes.Length;
            BytesPlusCount holder = new BytesPlusCount(bytes);
            m_DataQueue.Enqueue(new TRef(holder));
        }

        // Copy data out into a supplied buffer. If fPeek is true, it means we
        // would copy out the exact same bytes if called again.
        public int CopyFromHead(byte[] buffer, int offset, int length, bool fPeek)
        {
            int bytesCopied = 0;

            while ((m_DataQueue.Count > 0) && (bytesCopied < length)) {
                // Don't dequeue just yet, just peek
                TRef wrapper = (TRef)m_DataQueue.Peek();
                VTable.Assert(wrapper != null); // Because we checked the count
                BytesPlusCount topChunk = (BytesPlusCount)(wrapper.Acquire());

                int copied = topChunk.CopyOut(buffer, offset + bytesCopied,
                                              length - bytesCopied, fPeek);
                bytesCopied += copied;

                if ((!fPeek) && (topChunk.Empty)) {
                    // We want to throw away the top chunk. To take pressure off
                    // the finalizer, we'll explicitly free the ExHeap data vector.
                    topChunk.Dispose();
                    m_DataQueue.Dequeue();
                }
                else if ((!fPeek) && (!topChunk.Empty)) {
                    // This should only happen because we filled up the
                    // caller's buffer
                    Debug.Assert(bytesCopied == length);
                    // Put the data back into its wrapper
                    wrapper.Release(topChunk);
                }
                else {
                    // Release topChunk back
                    wrapper.Release(topChunk);
                }
            }

            if (!fPeek) {
                m_Count -= bytesCopied;
                Debug.Assert(m_Count >= 0);
            }

            return bytesCopied;
        }

        public int Count
        {
            get { return m_Count; }
        }
    }
}

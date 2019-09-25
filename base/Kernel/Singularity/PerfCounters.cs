////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PerfCounters.cs
//
//  Note:
//

using System;
using System.GCs;
using System.Collections;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Xml;
using Microsoft.Singularity.Loader;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Scheduling;

using Microsoft.Singularity.V1.Threads;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.Security;

namespace Microsoft.Singularity
{
    [CLSCompliant(false)]
    public class PerfCounters
    {
        private static long threadsCreated; 
        private static long bytesSent; 
        private static long msgsSent; 
        private static long channelsCreated; 
        

        public static void Initialize() {
            threadsCreated = 0; 
            bytesSent = 0; 
            msgsSent = 0;
            channelsCreated = 0; 
        }

        public static void IncrementChannelsCreated() {
            Interlocked.Increment(ref channelsCreated); 
        } 

        public static long ChannelsCreated {
            get {
                return channelsCreated; 
            }
        }

        public static void IncrementThreadsCreated() {
            Interlocked.Increment(ref threadsCreated); 
        }

        public static long ThreadsCreated {
            get {
                return threadsCreated; 
            }
        }

        public static void AddBytesSent(long bytes) {
            bool iflag = Processor.DisableInterrupts();
            bytesSent += bytes;
            Processor.RestoreInterrupts(iflag);
        }

        public static long BytesSent {
            get {
                return bytesSent; 
            }
        }

        public static void IncrementMsgsSent() {
            Interlocked.Increment(ref msgsSent); 
        }

        public static long MsgsSent {
            get {
                return msgsSent; 
            }
        }
    }
    
}

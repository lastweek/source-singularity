////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ServiceThread.cs
//
//  Note:
//

using System.Threading;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity
{
    ///
    /// <summary>
    ///     Class processing asynchronous requeusts
    /// </summary>
    ///
    public class ServiceThread
    {
        internal static void Initialize()
        {
            queue = new ServiceRequestQueue();
            Thread.CreateThread(Thread.CurrentProcess, new ThreadStart(ServiceLoop)).Start();
        }

        ///
        /// <summary>
        ///     Enqueue a request into the service queue
        /// </summary>
        ///
        /// <param name="req">Requeuest to enqueu</param>
        ///
        [NoHeapAllocation]
        internal static void Request(ServiceRequest req)
        {
            // Dequeue the request
            queue.Enqueue(req);
        }

        ///
        /// <summary>
        ///     Service thread loop processing requests
        /// </summary>
        ///
        private static void ServiceLoop()
        {
            while (true) {

                ServiceRequest req = queue.Dequeue();

                req.Service();
            }
        }

        /// <summary> Service queue </summary>
        private static ServiceRequestQueue  queue;

    }
}

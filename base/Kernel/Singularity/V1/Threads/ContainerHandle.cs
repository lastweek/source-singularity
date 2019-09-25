////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ContainerHandle.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity.V1.Threads
{
    [CLSCompliant(false)]
    public struct ContainerHandle
    {
        public readonly UIntPtr id;

        public static readonly ContainerHandle Zero = new ContainerHandle();

        internal ContainerHandle(UIntPtr id)
        {
            this.id = id;
        }

        [ExternalEntryPoint]
        public static unsafe bool CreateImpl(ContainerHandle * container)
        {
            return Create(out *container);
        }

        public static bool Create(out ContainerHandle container)
        {
            container = new ContainerHandle(Thread.CurrentProcess.AllocateHandle());

            Tracing.Log(Tracing.Debug, "ContainerHandle.Create(out id={0:x8})",
                        container.id);
            return true;
        }

        [ExternalEntryPoint]
        public static void Dispose(ContainerHandle container)
        {
            Tracing.Log(Tracing.Debug, "ContainerHandle.Dispose(id={0:x8})",
                        container.id);

            Thread.CurrentProcess.ReleaseHandle(container.id);
        }
    }
}

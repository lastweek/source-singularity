///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   HalTimer.cs
//

using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Hal
{
    public abstract class HalTimer
    {
        /// <value>
        /// Maximum value accepted by SetNextInterrupt.
        /// </value>
        public abstract TimeSpan MaxInterruptInterval {
            [NoHeapAllocation]
            get;
        }

        /// <value>
        /// Minimum value accepted by SetNextInterrupt.
        /// </value>
        public abstract TimeSpan MinInterruptInterval {
            [NoHeapAllocation]
            get;
        }

        /// <summary>
        /// Clear interrupt associated with timer.
        /// </summary>
        [NoHeapAllocation]
        public abstract void ClearInterrupt();

        /// <summary>
        /// Set relative time of next interrupt.
        ///
        /// <param name="delta">
        /// Relative time of next interrupt.
        /// The time should be with the range between from <c>SetNextInterruptMinDelta</c> to
        /// <c>SetNextInterruptMaxDelta</c></param>.
        /// </summary>
        [NoHeapAllocation]
        public abstract void SetNextInterrupt(TimeSpan delta);
    }

} // namespace Microsoft.Singularity.Hal

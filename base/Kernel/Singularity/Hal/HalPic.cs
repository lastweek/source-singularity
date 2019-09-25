///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   HalPic.cs
//
//  Note:
//

using System;
using System.Collections;
using System.Runtime.CompilerServices;
using System.Threading;

namespace Microsoft.Singularity.Hal
{
    public abstract class HalPic
    {
        /// <summary>
        /// Maximum valid IRQ property.  On legacy PC systems this value is
        /// 15.  On APIC PC systems this number will usually be larger.
        /// </summary>
        public abstract byte MaximumIrq
        {
            [NoHeapAllocation] get;
        }

        /// <summary>
        /// Convert interrupt vector to interrupt request line.
        /// </summary>
        [NoHeapAllocation]
        public abstract byte InterruptToIrq(byte interrupt);

        /// <summary>
        /// Convert interrupt request line to interrupt vector.
        /// </summary>
        [NoHeapAllocation]
        public abstract byte IrqToInterrupt(byte irq);

        /// <summary>
        /// Acknowledge the interrupt request.  (EOI)
        /// </summary>
        [NoHeapAllocation]
        public abstract void AckIrq(byte irq);

        /// <summary>
        /// Enable interrupt request by removing mask.
        /// </summary>
        [NoHeapAllocation]
        public abstract void EnableIrq(byte irq);

        /// <summary>
        /// Disable interrupt request by applying mask.
        /// </summary>
        [NoHeapAllocation]
        public abstract void DisableIrq(byte irq);

        /// <summary>
        /// Acknowledge and mask interrupt.
        /// </summary>
        [NoHeapAllocation]
        public abstract void ClearInterrupt(byte interrupt);
    }
} // namespace Microsoft.Singularity.Hal

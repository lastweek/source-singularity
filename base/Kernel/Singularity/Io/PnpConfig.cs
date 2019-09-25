///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PnpConfig.cs
//
//  Note:
//

using System;
using System.Text;
using System.Collections;
using Microsoft.Singularity;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public class PnpConfig : IoConfig
    {
        internal PnpConfig(String[] ids, IoRange[] ranges, IoRange [] fixedRanges)
        {
            this.Ids = ids;
            this.DynamicRanges = ranges;
            this.FixedRanges = fixedRanges;
        }

        // HACK: switched from internal to public
        public PnpConfig(String[] ids, IoRange[] ranges)
        {
            this.Ids = ids;
            this.DynamicRanges = ranges;
            this.FixedRanges = null;
        }

        public PnpConfig(String[] ids, ArrayList rangeList)
        {
            this.Ids = ids;
            this.FixedRanges = null;

            if (rangeList != null) {
                DynamicRanges = new IoRange [rangeList.Count];

                int o = 0;

                // We copy out in the following order: IoMemory, Ports, IRQ,
                // DMA.

                for (int i = 0; i < rangeList.Count; i++) {
                    if (rangeList[i] is IoMemoryRange) {
                        DynamicRanges[o++] = (IoRange)rangeList[i];
                    }
                }
                for (int i = 0; i < rangeList.Count; i++) {
                    if (rangeList[i] is IoPortRange) {
                        DynamicRanges[o++] = (IoRange)rangeList[i];
                    }
                }
                for (int i = 0; i < rangeList.Count; i++) {
                    if (rangeList[i] is IoIrqRange) {
                        DynamicRanges[o++] = (IoRange)rangeList[i];
                    }
                }
                for (int i = 0; i < rangeList.Count; i++) {
                    if (rangeList[i] is IoDmaRange) {
                        DynamicRanges[o++] = (IoRange)rangeList[i];
                    }
                }
            }
            else {
                DynamicRanges = new IoRange [0];
            }

            Tracing.Log(Tracing.Audit, "{0}", ToPrint());
        }

        public override string ToString()
        {
            return "[PNP " + this.Ids[0] + "]";
        }
    }
} // end namespace Microsoft.Singularity.Io

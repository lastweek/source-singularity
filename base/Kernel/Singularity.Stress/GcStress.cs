////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   GcStress.cs
//
//  Note:   Simple Singularity test program.
//  Warning: this file is compiled in two separate places:
//    - Applications/Tests/GcStress
//    - Kernel/Singularity.Stress

using System;
using System.Collections;

namespace Microsoft.Singularity.Stress
{
    public abstract class GcStress
    {
        private void GcStressVariableSizeObjects()
        {
            const uint maxItemBytes = 65535;
            const uint maxAllocatedBytes = 1000000;
            byte dummy = 0;

            Print("Running variable size object test.");

            DateTime start     = DateTime.Now;
            TimeSpan duration  = TimeSpan.FromSeconds(10);
            TimeSpan oneSecond = TimeSpan.FromSeconds(1);

            Queue q = new Queue();
            while (DateTime.Now - start < duration) {
                DateTime roundStart = DateTime.Now;
                uint iterations = 0;
                while (DateTime.Now - roundStart < oneSecond) {
                    uint allocatedBytes = 0;
                    uint i = 17u * iterations;
                    while (allocatedBytes < maxAllocatedBytes) {
                        uint itemBytes = 1u + (uint)((433777u * i) % maxItemBytes);
                        allocatedBytes += itemBytes;
                        i++;
                        byte [] data = new byte[itemBytes];
                        data[0] = 0xff;
                        q.Enqueue(data);
                    }

                    while (q.Count != 0) {
                        byte []! data = (!)(byte []) q.Dequeue();
                        dummy ^= data[0];
                    }
                    iterations ++;
                }
                Print(String.Format(" {0}", iterations, dummy));
            }
            Print("\n");
        }

        private void GcStressFixedSizeObjects()
        {
            const int itemCount = 1024;
            const int itemBytes = 1024;

            Print("Running fixed size object test.");

            byte dummy = 0;

            DateTime start     = DateTime.Now;
            TimeSpan duration  = TimeSpan.FromSeconds(10);
            TimeSpan oneSecond = TimeSpan.FromSeconds(1);

            Queue q = new Queue();
            while (DateTime.Now - start < duration) {
                DateTime roundStart = DateTime.Now;
                int iterations = 0;
                while (DateTime.Now - roundStart < oneSecond) {
                    for (int i = 0; i < itemCount; i++) {
                        byte [] data = new byte[itemBytes];
                        // Debug.Assert(data[0] == 0);
                        data[0] = 0xff;
                        q.Enqueue(data);
                    }

                    for (int i = 0; i < itemCount; i++) {
                        byte []! data = (!)(byte []) q.Dequeue();
                        // Debug.Assert(data[0] == 0xff);
                        dummy ^= data[0];
                    }
                    iterations ++;
                }
                Print(String.Format(" {0}", iterations, dummy));
            }
            Print("\n");
        }

        protected abstract void Print(string! s);

        //[ShellCommand("gcstress", "Stress garbage collector")]
        public void Run()
        {
            GcStressFixedSizeObjects();
            GcStressVariableSizeObjects();
        }
    }
}

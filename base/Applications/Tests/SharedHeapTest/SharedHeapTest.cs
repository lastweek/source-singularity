///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note: User-mode test program for calling shared heap through the ABI.
//

using Microsoft.Singularity.V1.Services;
using System;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity.Channels;
using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal Parameters();

        internal int AppMain() {
            SharedHeapTest.AppMain(this);
            return 0;
        }
    }

    unsafe public class SharedHeapTest
    {
        //
        // Note: The integrity check relies on there being one bit in each byte
        // to represent the owning concurrent allocation slot, so the number of
        // concurrent allocations can't exceed 8.
        //
        private const uint ConcurrentAllocations = 8;
        private SharedHeapService.Allocation*[]! mem;

        Random! random = new Random();

        internal static void AppMain(Parameters! config)
        {
            SharedHeapTest test = new SharedHeapTest();

            uint Iterations = 10;

            Console.WriteLine("Starting Shared Heap Test\n");
            test.StartUp();
            for (uint loop = 0; loop < Iterations; loop++) {
                test.Perturb();
                if (test.Check() == false) {
                    break;
                }
            }
        }

        private SharedHeapTest() {
            //
            // Create an array to hold our concurrent allocations.
            //
            this.mem = new SharedHeapService.Allocation*[ConcurrentAllocations];
        }

        public static void Usage()
        {
            Console.WriteLine("Usage: sharedheap [Iterations]\n");
        }

        public void StartUp()
        {
            //
            // Allocating a bunch of randomly sized things.
            //
            for (uint loop = 0; loop < ConcurrentAllocations; loop++) {
                AllocRandomSizedThingy(loop);
                if (CheckForValue(loop, 0) == true) {
                    Console.WriteLine("Passed zero-fill test.\n");
                }
                else {
                    Console.WriteLine("Failed zero-fill test.\n");
                }
                FillWithValue(loop, (byte)(1 << (int)loop));
            }
        }

        public bool Check()
        {
            //
            // Check all allocations for expected bit settings.
            //
            Console.WriteLine("--------\n");
            Console.WriteLine("Integrity Check\n");

            for (uint loop = 0; loop < ConcurrentAllocations; loop++) {
                if (CheckBits(loop, (byte)(1 << (int)loop)) == false) {
                    return false;
                }
            }

            Console.WriteLine("--------\n");
            return true;
        }

        public void Perturb()
        {
            //
            // Pick an element slot to use and an action to take.
            //
            uint which = (uint)random.Next(ConcurrentAllocations);
            uint action = (uint)random.Next(3);

            //
            // Free up the slot.
            //
            Console.WriteLine("--------\n");
            Console.WriteLine(
                "Freeing region: Data = {0}, Size = {1}.\n",
                SharedHeapService.GetData(this.mem[which]),
                SharedHeapService.GetSize(this.mem[which]));

            ClearBits(which, (byte)(1 << (int)which));
            SharedHeapService.Free(this.mem[which]);

            Console.WriteLine("--------\n");

            //
            // Play around.
            //
            switch (action) {
                case 0:
                    //
                    // Allocate something new.
                    //
                    Console.WriteLine("Allocation Test\n");
                    AllocRandomSizedThingy(which);
                    if (CheckForValue(which, 0) == true) {
                        Console.WriteLine("Passed zero-fill test.\n");
                    }
                    else {
                        Console.WriteLine("Failed zero-fill test.\n");
                    }

                    //
                    // Store bit corresponding to slot number in each
                    // data byte.  Used to check integrity later.
                    //
                    FillWithValue(which, (byte)(1 << (int)which));
                    break;

                case 1:
                    //
                    // Split an element in two.  Use the slot we freed
                    // up above to hold the split-off piece.
                    //
                    Console.WriteLine("Split Test\n");

                    //
                    // Pick a region to split.
                    //
                    uint split;
                    do {
                        split = (uint)random.Next(ConcurrentAllocations);
                    } while (split == which);

                    Console.Write(
                        "Splitting region: Data = {0}, Size = {1}",
                        SharedHeapService.GetData(this.mem[split]),
                        SharedHeapService.GetSize(this.mem[split]));
                    UIntPtr offset = (UIntPtr)random.Next(
                        1,
                        (int)SharedHeapService.GetSize(this.mem[split]));
                    Console.WriteLine(" in two at offset {0}.\n", offset);

                    this.mem[which] = SharedHeapService.Split(
                        this.mem[split],
                        offset);

                    Console.WriteLine(
                        "Revised region: Data = {0}, Size = {1}.\n",
                        SharedHeapService.GetData(this.mem[split]),
                        SharedHeapService.GetSize(this.mem[split]));

                    Console.WriteLine(
                        "New region: Data = {0}, Size = {1}.\n",
                        SharedHeapService.GetData(this.mem[which]),
                        SharedHeapService.GetSize(this.mem[which]));

                    //
                    // Remove bit corresponding to the slot of the original
                    // region from the split-off data.  Likewise, add the
                    // bit corresponding to the slot number of the split-off
                    // region to the split-off data.
                    //
                    ClearBits(which, (byte)(1 << (int)split));
                    SetBits(which, (byte)(1 << (int)which));

                    break;

                case 2:
                    //
                    // Share part of a region.  Use the slot we freed
                    // up above to hold the shared piece.
                    //
                    Console.WriteLine("Share Test\n");

                    //
                    // Pick a region to share.
                    //
                    uint share;
                    do {
                        share = (uint)random.Next(ConcurrentAllocations);
                    } while (share == which);

                    Console.Write(
                        "Sharing region: Data = {0}, Size = {1}",
                        SharedHeapService.GetData(this.mem[share]),
                        SharedHeapService.GetSize(this.mem[share]));
                    UIntPtr start = (UIntPtr)random.Next(
                        1,
                        (int)SharedHeapService.GetSize(this.mem[share]));
                    Console.WriteLine(" starting at offset {0}.\n", start);

                    this.mem[which] = SharedHeapService.Share(
                        this.mem[share],
                        start, SharedHeapService.GetSize(this.mem[share]));

                    Console.WriteLine(
                        "Original region: Data = {0}, Size = {1}.\n",
                        SharedHeapService.GetData(this.mem[share]),
                        SharedHeapService.GetSize(this.mem[share]));

                    Console.WriteLine(
                        "New region: Data = {0}, Size = {1}.\n",
                        SharedHeapService.GetData(this.mem[which]),
                        SharedHeapService.GetSize(this.mem[which]));

                    //
                    // Modify each data byte in the shared region to include
                    // the bit corresponding to the slot number of the new
                    // shared allocation handle.
                    //
                    SetBits(which, (byte)(1 << (int)which));

                    break;
            }
        }

        private void AllocRandomSizedThingy(uint index)
        {
            // REVIEW: We can't ask the system for the PageSize?
            // Hardcoded to 2 * Pages.PageSize.
            UIntPtr size = (UIntPtr)random.Next(1, 8192);

            this.mem[index] = SharedHeapService.Allocate(size, typeof(byte).GetSystemType(), 0);

            Console.WriteLine("Allocated region: Data = {0}, Size = {1}.\n",
                              SharedHeapService.GetData(this.mem[index]),
                              SharedHeapService.GetSize(this.mem[index]));
        }

        private void FillWithValue(uint index, byte value)
        {
            UIntPtr data = SharedHeapService.GetData(this.mem[index]);
            UIntPtr size = SharedHeapService.GetSize(this.mem[index]);

            for (UIntPtr address = data; address < data + size; address++) {
                *(byte *)address = value;
            }

            return;
        }

        private bool CheckForValue(uint index, byte value)
        {
            UIntPtr data = SharedHeapService.GetData(this.mem[index]);
            UIntPtr size = SharedHeapService.GetSize(this.mem[index]);
            bool status = true;

            for (UIntPtr address = data; address < data + size; address++) {
                if (*(byte *)address != value) {
                    status = false;
                    Console.Write("Wrong value {0} at address {1}.\n",
                                      *(byte *)address, address);
                    Console.Write("Should be {0}.\n", value);
                }
            }

            return status;
        }

        private void SetBits(uint index, byte bit)
        {
            UIntPtr data = SharedHeapService.GetData(this.mem[index]);
            UIntPtr size = SharedHeapService.GetSize(this.mem[index]);

            for (UIntPtr address = data; address < data + size; address++) {
                *(byte *)address |= bit;
            }

            return;
        }

        private void ClearBits(uint index, byte bit)
        {
            UIntPtr data = SharedHeapService.GetData(this.mem[index]);
            UIntPtr size = SharedHeapService.GetSize(this.mem[index]);

            for (UIntPtr address = data; address < data + size; address++) {
                *(byte *)address &= (byte)~bit;
            }

            return;
        }

        private bool CheckBits(uint index, byte bit)
        {
            UIntPtr data = SharedHeapService.GetData(this.mem[index]);
            UIntPtr size = SharedHeapService.GetSize(this.mem[index]);
            bool status = true;

            for (UIntPtr address = data; address < data + size; address++) {
                if ((*(byte *)address & bit) != bit) {
                    status = false;
                    Console.WriteLine("Bad value {0} at address {1}.\n",
                                      *(byte *)address, address);
                    //
                    // Stop at one to prevent huge output.
                    //
                    break;
                }
            }

            return status;
        }
    }
}


// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
// Simple PE Loader for Singularity
//
// Currently does not support:
//      x64
//      sections loaded at separate addresses
//      loading at preferred address

// #define verbose

//#define SINGULARITY_ASMP

namespace Microsoft.Singularity.Loader
{
    using Microsoft.Singularity;
    using Microsoft.Singularity.Io;

    using System;
    using System.Runtime.InteropServices;
    using System.Threading;

    internal class Relocations
    {
        private const ushort sizeofBaseRelocation = 8;

        //Based relocation types.
        private const ushort IMAGE_REL_BASED_ABSOLUTE      = 0;
        private const ushort IMAGE_REL_BASED_HIGH          = 1;
        private const ushort IMAGE_REL_BASED_LOW           = 2;
        private const ushort IMAGE_REL_BASED_HIGHLOW       = 3;
        private const ushort IMAGE_REL_BASED_HIGHADJ       = 4;
        private const ushort IMAGE_REL_BASED_DIR64         = 10;

        internal static void FixupBlocks(IoMemory relocationMemory, int relocOffset,
                                         IoMemory codeMemory, UIntPtr diff)
        {
            uint va = relocationMemory.Read32Unchecked(relocOffset);
            uint size = relocationMemory.Read32Unchecked(relocOffset+4);
            while (0 != va) {
#if verbose
                DebugStub.WriteLine(" FixUpBlocks: addr={0:x8}, size={1:x8}, roffset={2:x8} ",
                                    __arglist(va, size,relocOffset));
#endif

#if SINGULARITY_ASMP
                if (va == 0xffffffff || size == 0xffffffff
                    ||
                    va >= 0xc0000000 || size >= 0xc0000000) {
                    break;
                }
#endif
                FixupBlock(relocationMemory, relocOffset,
                           codeMemory, diff, va, (int)size);
                relocOffset += (int)size;
                va = relocationMemory.Read32Unchecked(relocOffset);
                size  = relocationMemory.Read32Unchecked(relocOffset+4);
            }
        }

        private static void FixupBlock(IoMemory relocationMemory, int relocOffset,
                                       IoMemory codeMemory, UIntPtr diff, uint va, int size)
        {
            ushort  fixupEntry;

            // Compute number of entries
            int numberOfEntries = (size - sizeofBaseRelocation) /2;
#if verbose
            DebugStub.WriteLine(" FixUp: addr={0:x8}, size={1:x8}, count={2}",
                                __arglist(va, size,  numberOfEntries));
#endif
            int currentSize = size - sizeofBaseRelocation;
            relocOffset += sizeofBaseRelocation;   //skip block header
            for (int i = 0; i < numberOfEntries; i++) {
                fixupEntry = relocationMemory.Read16(relocOffset);
                relocOffset += 2;
                currentSize -= 2;
                ushort type = (ushort) (fixupEntry >>12);
                //clear out the upper bits
                uint rVA  =  (uint)(fixupEntry & 0xfff)+ va;
                if (IMAGE_REL_BASED_ABSOLUTE == type) {
                    //DebugStub.WriteLine("        type={0:x4}      rVA={1:x8}",
                    //__arglist(type, rVA));
                    // hit an alignment type. there should be no more entries
                    //DebugStub.WriteLine("   fixup:  count ={0}, loop count ={1} size={2}",
                    //__arglist(numberOfEntries, i, currentSize));
                    break;
                }
                else if (IMAGE_REL_BASED_HIGHLOW == type) {
                    // get 32-bit word pointed by rVA
                    // mem object representing loaded image is 0 based rVA is sufficient
                    uint fixupItem = codeMemory.Read32Unchecked((int)rVA);
                    uint newValue = unchecked((uint) diff + (uint) fixupItem);
#if verbose
                    DebugStub.WriteLine("        Fixup: rVA={0:x8} value={1:x8} diff={2:x8}, newValue={3:x8}",
                                        __arglist(rVA, fixupItem, diff, newValue));
#endif
                    codeMemory.Write32Unchecked((int) rVA, newValue);
                }
                else if (IMAGE_REL_BASED_DIR64 == type) {
                    ulong OldValue;
                    ulong NewValue;

                    OldValue = codeMemory.Read64((int) rVA);

                    NewValue = unchecked(OldValue + (ulong) diff);

                    codeMemory.Write64((int) rVA, NewValue);
                }
                else {
                    DebugStub.WriteLine("PE Bad fixup: %x", __arglist(type));
                    DebugStub.Break();
                }
            }
            //DebugStub.WriteLine();
        }
    }
}

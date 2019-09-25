//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


namespace System.GCs {

    using System.Runtime.CompilerServices;
#if SINGULARITY
    using Microsoft.Singularity;
#endif

    // REVIEW: This should probably only be on the mixin types to
    // CalleeSaveRegisters, but it seems to be lost if put there.
    [AccessedByRuntime("referenced from halforgc.asm")]
    internal struct CalleeSaveRegisters
    {

        internal void DebugTrace()
        {
            // Placeholder for an override method
        }

        internal UIntPtr GetFramePointer()
        {
            // Placeholder for an override method
            return UIntPtr.Zero;
        }

    }

    internal unsafe struct CalleeSaveLocations {

#if SINGULARITY_KERNEL
        internal void SetCalleeSaves(ThreadContext *context)
        {
            // Placeholder for an override method
        }
#endif

        internal void SetCalleeSaves(CalleeSaveRegisters *calleeSaveRegisters)
        {
            // Placeholder for an override method
        }

        internal void ClearCalleeSaves()
        {
            // Placeholder for an override method
        }

        [PreInitRefCounts]
        internal void ScanLiveRegs(UIntPtr mask,
                                   NonNullReferenceVisitor referenceVisitor)
        {
            // Placeholder for an override method
        }

        internal void PopFrame(UIntPtr *framePointer,
                               UIntPtr calleeSaveMask,
                               bool framePointerOmitted,
                               bool hasTransitionRecord)
        {
            // Placeholder for an override method
        }

        internal void ClearFrame(UIntPtr calleeSaveMask,
                                 bool framePointerOmitted)
        {
            // Placeholder for an override method
        }

        internal UIntPtr GetFramePointer()
        {
            // Placeholder for an override method
            return UIntPtr.Zero;
        }

        internal struct RegLocation
        {

            [Inline]
            internal void SetCalleeReg(UIntPtr *regField)
            {
                this.pending = false;
                this.value = *regField;
                this.head = regField;
                *regField = UIntPtr.Zero;
            }

            internal void ClearCalleeReg()
            {
                VTable.Deny(this.pending);
                UIntPtr *scan = this.head;
                while (scan != null) {
                    UIntPtr temp = *scan;
                    *scan = value;
                    scan  = (UIntPtr *) temp;
                }
                this.head = null;
            }

            [PreInitRefCounts]
            internal void ScanLiveReg(uint kind,
                                      NonNullReferenceVisitor visitor)
            {
                switch (kind) {
                  case 0: {
                      // Value is not a traceable heap pointer
                      break;
                  }
                  case 1: {
                      // Value is a pointer variable
                      VTable.Deny(this.head == null);
                      if (value != UIntPtr.Zero) {
                          fixed (UIntPtr *valueField = &this.value) {
                              visitor.Visit(valueField);
                          }
                      }
                      ClearCalleeReg();
                      break;
                  }
                  case 2: {
                      // Value is unchanged since function entry
                      VTable.Deny(this.pending);
                      this.pending = true;
                      break;
                  }
                  case 3:
                  default: {
                      VTable.NotReached("ScanLiveReg 3 or default");
                      break;
                  }
                }
            }

            internal void PopFrameReg(ref UIntPtr *calleeSaveStart)
            {
                if (this.head != null && !this.pending) {
                    ClearCalleeReg();
                }
                if (this.head == null) {
                    this.value = *calleeSaveStart;
                } else {
                    VTable.Assert(this.pending, "pending should be true");
                    VTable.Assert(*calleeSaveStart == this.value,
                                  "values are not equal");
                }
                this.pending = false;
                *calleeSaveStart = (UIntPtr) this.head;
                this.head = calleeSaveStart;
                calleeSaveStart--;
            }

            internal void ClearFrameReg() {
                UIntPtr *scan = this.head;
                while (scan != null) {
                    UIntPtr temp = *scan;
                    *scan = value;
                    scan = (UIntPtr *) temp;
                }
                this.head = null;
                this.pending = false;
                this.value = UIntPtr.Zero;
            }

            internal bool pending;
            internal UIntPtr value;
            internal UIntPtr *head;

        }

        CalleeSaveLocations.RegLocation FramePointer;

    }

}

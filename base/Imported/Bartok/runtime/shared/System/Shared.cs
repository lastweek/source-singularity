//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

// This code is used in both mscorlibOverride and for building applications
// (in particular Bartok). This makes sure the constant used in Bartok
// compiler and mscorlibOverride are the same

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Bartok.Runtime {
#if SINGULARITY
    [AccessedByRuntime("Referenced from C++")]
#endif
    public enum StructuralType {
        None            = 0x00,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        Reference       = 0x01,
        UntracedPointer = 0x02,
        Struct          = 0x03,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        Bool            = 0x04,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        Char            = 0x05,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        Int8            = 0x06,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        Int16           = 0x07,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        Int32           = 0x08,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        Int64           = 0x09,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        UInt8           = 0x0a,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        UInt16          = 0x0b,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        UInt32          = 0x0c,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        UInt64          = 0x0d,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        Float32         = 0x0e,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        Float64         = 0x0f,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        IntPtr          = 0x10,
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        UIntPtr         = 0x11,
        Void            = 0x12,
    };

    public enum GCType{
        AdaptiveCopyingCollector            = 0x00,
        MarkSweepCollector                  = 0x01,
        SemispaceCollector                  = 0x02,
        SlidingCollector                    = 0x03,
        ReferenceCountingCollector          = 0x04,
        ConcurrentMSCollector               = 0x05,
        DeferredReferenceCountingCollector  = 0x06,
        NullCollector                       = 0x07,
        AtomicRCCollector                   = 0x08,
        TableMarkSweepCollector             = 0x09,
        CoCoMSCollector                     = 0x0a
    };

    public enum PTType{
        CentralPT = 0,
        CentralPTHimem,
        FlatDistributedPT,
        FlatDistributedPTTest
    }; 

    public enum WBType {
        noWB                         = 0,
        Generational                 = 1,
        CMS                          = 2,
        ARC                          = 3,
        AllCards                     = 4,
        ExpandingCoCo                = 5,
        ProbabilisticCoCo            = 6,
        AbortingCoCo                 = 7,
        BrooksTest                   = 8,
        BrooksCMSTest                = 9,
    };
    
    public class BarrierMask {
        public class PathSpec {
            public const int AllowFast   = 1;
            public const int UseMask     = 2;
        }
        public class Forward {
            public const int Nullable    = 4;
            public const int Writable    = 8;
        }
    }

    public enum RemSetType {
        noRemSet                     = 0,
        SSB                          = 1,
        Cards                        = 2,
    };

    public enum CopyScanType {
        noCopyScan                   = 0,
        CheneyScan                   = 1,
        HierarchicalScan             = 2,
        NestedHierarchicalScan       = 3,
    };

#if SINGULARITY
    [AccessedByRuntime("Referenced from C++")]
#endif
    public class Constants {
      public const int TypeTestDisplaySize = 6;
      public const int TypeTestDisplayPosCache = TypeTestDisplaySize + 1;
#if true
      public const bool TypeTestDisplayIncludesObject = false;
      public const int TypeTestDisplayObjectOffset = 0;
#else
      public const bool TypeTestDisplayIncludesObject = true;
      public const int TypeTestDisplayObjectOffset = 1;
#endif
      public const int LargeObjectBits = 16;

      // shared by compact record
      public const int CompactEntryMaskStart = 6;
      public const int CompactArgMaskStart = 2;
      public const int CompactArgMask = 0xf;

      // shared by full record
      public const int FullEntryMaskStart = 1;
      public const int FullRecordMask = 0x7;

// ISA_ is the prefix used by Singularity for the system architecture
#if X86 || ISA_IX86
      // constants used by GC activation descriptor table entry
      public const int InbetweenSlotsAboveNoFP = 1;
      public const int InbetweenSlotsBelowNoFP = 0;
      public const int InbetweenSlotsAboveFP = 2;
      public const int InbetweenSlotsBelowFP = 0;

      public const int LastBitPos = 31;
      // Compact record Frame pointer omitted
      public const int CompactStackBitMaskStartNoFP = 24;
      public const int CompactEntryMaskNoFP = 0x1f;
      public const int CompactCalleeSaveUseStartNoFP = 11;
      public const int CompactCalleeSaveUseMaskNoFP = 0xff;
      public const int CompactFrameSizeStartNoFP = 19;
      public const int CompactFrameSizeMaskNoFP = 0x1f;

      // Compact record Use frame pointer
      public const int CompactStackBitMaskStartFP = 16;
      public const int CompactEntryMaskFP = 0xf;
      public const int CompactCalleeSaveUseStartFP = 10;
      public const int CompactCalleeSaveUseMaskFP = 0x3f;

      // Full record Frame pointer omitted.
      public const int FullEntryMaskNoFP = 0x1f;
      public const int FullPinnedPosNoFP = 17;
      public const int FullPinnedStartNoFP = 18;
      public const int FullCalleeSaveUseStartNoFP = 6;
      public const int FullCalleeSaveUseMaskNoFP = 0xff;
      public const int FullRecordSizePosNoFP = 14;
      public const int FullFrameSizeStartNoFP = 22;

      // Full record Use Frame pointer
      public const int FullEntryMaskFP = 0xf;
      public const int FullPinnedPosFP = 14;
      public const int FullPinnedStartFP = 15;
      public const int FullCalleeSaveUseStartFP = 5;
      public const int FullCalleeSaveUseMaskFP = 0x3f;
      public const int FullRecordSizePosFP = 11;

// ISA_ is the prefix used by Singularity for the system architecture
#elif AMD64 || ISA_IX64
      // constants used by GC activation descriptor table entry
      public const int InbetweenSlotsAboveNoFP = 1;
      public const int InbetweenSlotsBelowNoFP = 0;
      public const int InbetweenSlotsAboveFP = 2;
      public const int InbetweenSlotsBelowFP = 0;

      public const int LastBitPos = 63;
      // Compact record Frame pointer omitted
      public const int CompactStackBitMaskStartNoFP = 36;
      public const int CompactEntryMaskNoFP = 0x1ff;
      public const int CompactCalleeSaveUseStartNoFP = 15;
      public const int CompactCalleeSaveUseMaskNoFP = 0xffff;
      public const int CompactFrameSizeStartNoFP =31;
      public const int CompactFrameSizeMaskNoFP = 0x1f;

      // Compact record Use frame pointer
      public const int CompactStackBitMaskStartFP = 28;
      public const int CompactEntryMaskFP = 0xff;
      public const int CompactCalleeSaveUseStartFP = 14;
      public const int CompactCalleeSaveUseMaskFP = 0x3fff;

      // Full record Frame pointer omitted
      public const int FullEntryMaskNoFP = 0x1ff;
      public const int FullPinnedPosNoFP = 29;
      public const int FullPinnedStartNoFP = 30;
      public const int FullCalleeSaveUseStartNoFP = 10;
      public const int FullCalleeSaveUseMaskNoFP = 0xffff;
      public const int FullRecordSizePosNoFP = 26;
      public const int FullFrameSizeStartNoFP = 38;

      // Full record Use Frame pointer
      public const int FullEntryMaskFP = 0xff;
      public const int FullPinnedPosFP = 26;
      public const int FullPinnedStartFP = 27;
      public const int FullCalleeSaveUseStartFP = 9;
      public const int FullCalleeSaveUseMaskFP = 0x3fff;
      public const int FullRecordSizePosFP = 23;

// ISA_ is the prefix used by Singularity for the system architecture
#elif ARM || ISA_ARM
// FIX
      // constants used by GC activation descriptor table entry
      public const int InbetweenSlotsAboveNoFP = 0;
      public const int InbetweenSlotsBelowNoFP = 2;
      public const int InbetweenSlotsAboveFP = 0;
      public const int InbetweenSlotsBelowFP = 3;

      public const int LastBitPos = 31;

      // Shared by all records
      public const int CompactMask = 0x1;

      // Compact record common constants
      public const int CompactOmitFPMask = 0x2;
      public const int CompactTransitionRecordMask = (0x1 << 6);

      // Compact record Frame pointer omitted
      // BUGBUG: The bridge does not support FPO.  These constants have not been fixed.
      public const int CompactStackBitMaskStartNoFP = 36;
      public const int CompactEntryMaskNoFP = 0x1f;
      public const int CompactCalleeSaveUseStartNoFP = 15;
      public const int CompactCalleeSaveUseMaskNoFP = 0xffff;
      public const int CompactFrameSizeStartNoFP =31;
      public const int CompactFrameSizeMaskNoFP = 0x1f;

      // Compact record Use frame pointer
      public const int CompactStackBitMaskStartFP = 16;
      public const int CompactEntryMaskFP = 0xf;
      public const int CompactCalleeSaveStartFP = 7;
      public const int CompactCalleeSaveMaskFP = 0x7;
      public const int CompactCalleeSaveUseStartFP = 10;
      public const int CompactCalleeSaveUseMaskFP = 0x3f;

      // Full record common constants
      public const int FullOmitFPMask = 0x1;
      public const int FullTransitionRecordMask = (0x1 << 1);


      // Full record Frame pointer omitted
      // BUGBUG: The bridge does not support FPO.  These constants have not been fixed.
      public const int FullEntryMaskNoFP = 0x3ff;
      public const int FullPinnedPosNoFP = 29;
      public const int FullPinnedStartNoFP = 30;
      public const int FullCalleeSaveUseStartNoFP = 10;
      public const int FullCalleeSaveUseMaskNoFP = 0xffff;
      public const int FullRecordSizePosNoFP = 26;
      public const int FullFrameSizeStartNoFP = 38;

      // Full record Use Frame pointer
      public const int FullEntryMaskFP = 0xff;
      public const int FullPinnedPosFP = 26;
      public const int FullPinnedStartFP = 27;
      public const int FullCalleeSaveStartFP = 2;
      public const int FullCalleeSaveMaskFP = 0x7f;
      public const int FullCalleeSaveUseStartFP = 9;
      public const int FullCalleeSaveUseMaskFP = 0x3fff;
      public const int FullRecordSizePosFP = 23;
#else
#error Undefined architecture
#endif

        // Workaround for lack of enum printing in Bartok
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        public static string[] StructuralTypeNames = {
            "None",
            "Reference",
            "UntracedPointer",
            "Struct",
            "Bool",
            "Char",
            "Int8",
            "Int16",
            "Int32",
            "Int64",
            "UnsignedInt8",
            "UnsignedInt16",
            "UnsignedInt32",
            "UnsignedInt64",
            "Float32",
            "Float64",
            "IntPtr",
            "UIntPtr",
            "Void",
        };

        // BUGBUG: what about entry for structs?
#if SINGULARITY
        [AccessedByRuntime("Referenced from C++")]
#endif
        public int[] arrayOfStride = {
            0,
            4,
            4,
            0,
            1,
            2,
            1,
            2,
            4,
            8,
            1,
            2,
            4,
            8,
            4,
            8,
            4,
            4,
            4,
        };
    };

#if !BARTOK_SYSTEM_EXTENSION
    [RequiredByBartok]
#endif
    public enum TypeInitState {
        Ready = 0,
        Running = 1,
        Failed = 2,
        Completed = 3
    };

    public enum StageControlOption {
        TryAllSupport = 0,
        InstrumentVirtualCalls = 1,
        PInvoke = 2,
    };
}


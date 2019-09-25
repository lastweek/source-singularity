///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  References:
//
//  - Third Generation Intel XScale Microarchitecture
//    Developer's Manual
//    May 2007
//    Order Number 316283-002US
//
//  - ARM Architecture Reference Manual
//    July 2005
//    ARM DDI 0100l
//

namespace Microsoft.Singularity.Isal.Arm.XScale
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    ///////////////////////////////////////////////////////////////////////////
    // Bit discriptors of first level descriptors.

    [CLSCompliant(false)]
    public struct L1
    {
        public const uint CoarsePageTableAddressMask   = 0xfffffc00;
        public const uint SectionAddressMask           = 0xfff00000;
        public const uint SupersectionAddressMask      = 0xff000000;
        public const uint SupersectionAddress35_32Mask = 0x00f00000;
        public const int  SupersectionAddress35_32Roll = 20;
        public const uint FinePageTableAddressMask     = 0xfffff000;

        public const uint InvalidSbz                   = 0xfffffffc;
        public const uint CoarsePageTableSbz           = 0x0000001e;
        public const uint SectionSbz                   = 0x000e8011;
        public const uint SupersectionSbz              = 0x000a81f1;
        public const uint FinePageTableSbz             = 0x0000c01c;

        public const uint TexMask                      = 0x00007000;
        public const int  TexRoll                      = 12;

        public const uint ApMask                       = 0x00000c00;
        public const int  ApRoll                       = 10;

        public const uint DomainMask                   = 0x000001e0;
        public const int  DomainRoll                   = 5;

        public const uint SBit                         = 0x00010000;
        public const uint PBit                         = 0x00000200;
        public const uint CBit                         = 0x00000008;
        public const uint BBit                         = 0x00000004;

        public const uint InvalidType                  = 0x00000000;
        public const uint CoarsePageTableType          = 0x00000001;
        public const uint SectionType                  = 0x00000002;
        public const uint SupersectionType             = 0x00040002;
        public const uint FinePageTableType            = 0x00000003;
        public const uint SupersectionTypeMask         = 0x00040003;
        public const uint TypeMask                     = 0x00000003;
    }

    ///////////////////////////////////////////////////////////////////////////
    // Bit discriptors of second level coarse descriptors.

    [CLSCompliant(false)]
    public struct L2Coarse
    {
        public const uint LargePageAddressMask          = 0xffff0000;
        public const uint SmallPageAddressMask          = 0xfffff000;
        public const uint ExtendedSmallPageAddressMask  = 0xfffff000;

        public const uint InvalidSbz                    = 0xfffffffc;
        public const uint ExtendedSmallPageSbz          = 0x00000200;

        public const uint LargePageSBit                 = 0x00008000;
        public const uint ExtendedSmallPageSBit         = 0x00000200;

        public const uint LargePageTexMask              = 0x00007000;
        public const int  LargePageTexRoll              = 12;
        public const uint ExtendedSmallPageTexMask      = 0x000001c0;
        public const int  ExtendedSmallPageTexRoll      = 6;

        public const uint Ap3Mask                       = 0x00000c00;
        public const int  Ap3Roll                       = 10;
        public const uint Ap2Mask                       = 0x00000300;
        public const int  Ap2Roll                       = 8;
        public const uint Ap1Mask                       = 0x000000c0;
        public const int  Ap1Roll                       = 6;
        public const uint Ap0Mask                       = 0x00000030;
        public const int  Ap0Roll                       = 4;

        public const uint CBit                          = 0x00000008;
        public const uint BBit                          = 0x00000004;

        public const uint InvalidType                   = 0x00000000;
        public const uint LargePageType                 = 0x00000001;
        public const uint SmallPageType                 = 0x00000002;
        public const uint ExtendedSmallPageType         = 0x00000003;
        public const uint TypeMask                      = 0x00000003;
    }

    ///////////////////////////////////////////////////////////////////////////
    // Access permissions

    [CLSCompliant(false)]
    public enum AccessPermission : uint
    {
        NoAccess       = 0,   // All accesses fault
        PrivilegedOnly = 1,
        UserReadOnly   = 2,   // Privileged full, User R/O
        FullAccess     = 3,
        Mask           = 3
    }

    ///////////////////////////////////////////////////////////////////////////

    [CLSCompliant(false)]
    public struct L1InvalidEntry
    {
        private uint descriptor;

        public static bool IsType(uint descriptor)
        {
            return IsValid.Get(descriptor, L1.InvalidType, L1.InvalidSbz);
        }

        public void Initialize()
        {
            this.descriptor = 0;
        }
    }

    ///////////////////////////////////////////////////////////////////////////

    [CLSCompliant(false)]
    public struct L1CoarsePageTableEntry
    {
        private uint descriptor;

        public static bool IsType(uint descriptor)
        {
            return IsValid.Get(descriptor,
                               L1.CoarsePageTableType,
                               L1.CoarsePageTableSbz);
        }

        public void Initialize(uint address)
        {
            this.descriptor = L1.CoarsePageTableType;
            this.Address    = address;
        }

        public bool Valid
        {
            get { return IsType(this.descriptor); }
        }

        public uint Address
        {
            get {
                return LxAddress.Get(this.descriptor,
                                     L1.CoarsePageTableAddressMask);
            }
            set {
                LxAddress.Set(ref this.descriptor,
                              L1.CoarsePageTableAddressMask,
                              value);
            }
        }

        public bool P
        {
            get {
                return LxBit.Get(this.descriptor, L1.PBit);
            }
            set {
                LxBit.Set(ref this.descriptor, L1.PBit, value);
            }
        }

        public uint Domain
        {
            get { return L1Domain.Get(this.descriptor); }
            set { L1Domain.Set(ref this.descriptor, value); }
        }
    }

    ///////////////////////////////////////////////////////////////////////////

    [CLSCompliant(false)]
    public struct L1SectionEntry
    {
        private uint descriptor;

        public static bool IsType(uint descriptor)
        {
            return IsValid.Get(descriptor, L1.SectionType, L1.SectionSbz);
        }

        public void Initialize(uint address)
        {
            this.descriptor = L1.SectionType;
            this.Address    = address;
        }

        public bool Valid
        {
            get { return IsType(this.descriptor); }
        }

        public uint Address
        {
            get {
                return LxAddress.Get(this.descriptor, L1.SectionAddressMask);
            }
            set {
                LxAddress.Set(ref this.descriptor,
                              L1.SectionAddressMask,
                              value);
            }
        }

        public bool S
        {
            get { return LxBit.Get(this.descriptor, L1.SBit); }
            set { LxBit.Set(ref this.descriptor, L1.SBit, value); }
        }

        public uint Tex
        {
            get { return L1Tex.Get(this.descriptor); }
            set { L1Tex.Set(ref this.descriptor, value); }
        }

        public AccessPermission AccessPermission
        {
            get { return L1AP.Get(this.descriptor); }
            set { L1AP.Set(ref this.descriptor, value); }
        }

        public bool P
        {
            get { return LxBit.Get(this.descriptor, L1.PBit); }
            set { LxBit.Set(ref this.descriptor, L1.PBit, value); }
        }

        public uint Domain
        {
            get { return L1Domain.Get(this.descriptor); }
            set { L1Domain.Set(ref this.descriptor, value); }
        }

        public bool C
        {
            get { return LxBit.Get(this.descriptor, L1.CBit); }
            set { LxBit.Set(ref this.descriptor, L1.CBit, value); }
        }

        public bool B
        {
            get { return LxBit.Get(this.descriptor, L1.BBit); }
            set { LxBit.Set(ref this.descriptor, L1.BBit, value); }
        }

        public bool Cacheable
        {
            get { return this.C; }
            set { this.C = value; }
        }

        public bool WriteThrough
        {
            get { return !this.B; }
            set { this.B = !value; }
        }
    }

    ///////////////////////////////////////////////////////////////////////////

    [CLSCompliant(false)]
    public struct L1SupersectionEntry
    {
        private uint descriptor;
        private const ulong AddressMask = 0xfff000000;

        public static bool IsType(uint descriptor)
        {
            return IsValid.Get(descriptor,
                               L1.SupersectionType,
                               L1.SupersectionSbz);
        }

        public void Initialize(ulong address)
        {
            this.descriptor = L1.SupersectionType;
            this.Address    = address;
        }

        public bool Valid
        {
            get { return IsType(this.descriptor); }
        }

        public ulong Address
        {
            get {
                uint l = this.descriptor & L1.SupersectionAddressMask;
                uint h = this.descriptor & L1.SupersectionAddress35_32Mask;
                return ((ulong)l) | (((ulong)h) << 12);
            }

            set {
                DebugStub.Assert((value & ~AddressMask) == 0);
                uint h = (uint)(value >> 12);
                uint l = (uint)(value & ((ulong)L1.SupersectionAddressMask));
                this.descriptor &= (L1.SupersectionAddressMask |
                                    L1.SupersectionAddress35_32Mask);
                this.descriptor |= (h|l);
            }
        }

        public bool S
        {
            get { return LxBit.Get(this.descriptor, L1.SBit); }
            set { LxBit.Set(ref this.descriptor, L1.SBit, value); }
        }

        public uint Tex
        {
            get { return L1Tex.Get(this.descriptor); }
            set { L1Tex.Set(ref this.descriptor, value); }
        }

        public AccessPermission AccessPermission
        {
            get { return L1AP.Get(this.descriptor); }
            set { L1AP.Set(ref this.descriptor, value); }
        }

        public bool P
        {
            get { return LxBit.Get(this.descriptor, L1.PBit); }
            set { LxBit.Set(ref this.descriptor, L1.PBit, value); }
        }

        public bool C
        {
            get { return LxBit.Get(this.descriptor, L1.CBit); }
            set { LxBit.Set(ref this.descriptor, L1.CBit, value); }
        }

        public bool B
        {
            get { return LxBit.Get(this.descriptor, L1.BBit); }
            set { LxBit.Set(ref this.descriptor, L1.BBit, value); }
        }

        public bool Cacheable
        {
            get { return this.C; }
            set { this.C = value; }
        }

        public bool WriteThrough
        {
            get { return !this.B; }
            set { this.B = !value; }
        }
    }

    ///////////////////////////////////////////////////////////////////////////

    [CLSCompliant(false)]
    public struct L1FineEntry
    {
        private uint descriptor;

        public static bool IsType(uint descriptor)
        {
            return IsValid.Get(descriptor,
                               L1.FinePageTableType,
                               L1.FinePageTableSbz);
        }

        public void Initialize(uint address)
        {
            this.descriptor = L1.FinePageTableType;
            this.Address    = address;
        }

        public bool Valid
        {
            get { return IsType(this.descriptor); }
        }

        public uint Address
        {
            get {
                return LxAddress.Get(this.descriptor, L1.SectionAddressMask);
            }
            set {
                LxAddress.Set(ref this.descriptor,
                              L1.SectionAddressMask,
                              value);
            }
        }

        public bool P
        {
            get { return LxBit.Get(this.descriptor, L1.PBit); }
            set { LxBit.Set(ref this.descriptor, L1.PBit, value); }
        }

        public uint Domain
        {
            get { return L1Domain.Get(this.descriptor); }
            set { L1Domain.Set(ref this.descriptor, value); }
        }
    }

    ///////////////////////////////////////////////////////////////////////////

    [CLSCompliant(false)]
    public struct L2CoarseInvalidEntry
    {
        private uint descriptor;

        public static bool IsType(uint descriptor)
        {
            return IsValid.Get(descriptor,
                               L2Coarse.InvalidType,
                               L2Coarse.InvalidSbz);
        }

        public void Initialize()
        {
            descriptor = 0;
        }
    }

    [CLSCompliant(false)]
    public struct L2CoarseLargeEntry
    {
        private uint descriptor;

        public static bool IsType(uint descriptor)
        {
            return IsValid.Get(descriptor, L2Coarse.LargePageType, 0);
        }

        public void Initialize(uint address)
        {
            this.descriptor = L2Coarse.LargePageType;
            this.Address    = address;
        }

        public uint Address
        {
            get {
                return LxAddress.Get(descriptor,
                                     L2Coarse.LargePageAddressMask);
            }
            set {
                LxAddress.Set(ref descriptor,
                              L2Coarse.LargePageAddressMask,
                              value);
            }
        }

        public bool S
        {
            get { return LxBit.Get(descriptor, L2Coarse.LargePageSBit); }
            set { LxBit.Set(ref descriptor, L2Coarse.LargePageSBit, value); }
        }

        public uint Tex
        {
            get {
                return LxBits.Get(descriptor,
                                  L2Coarse.LargePageTexMask,
                                  L2Coarse.LargePageTexRoll);
            }
            set {
                LxBits.Set(ref descriptor,
                           L2Coarse.LargePageTexMask,
                           L2Coarse.LargePageTexRoll,
                           value);
            }
        }

        public AccessPermission AP3
        {
            get {
                return (AccessPermission)
                    LxBits.Get(descriptor, L2Coarse.Ap3Mask, L2Coarse.Ap3Roll);
            }
            set {
                LxBits.Set(ref descriptor, L2Coarse.Ap3Mask, L2Coarse.Ap3Roll,
                           (uint)value);
            }
        }

        public AccessPermission AP2
        {
            get {
                return (AccessPermission)
                    LxBits.Get(descriptor, L2Coarse.Ap2Mask, L2Coarse.Ap2Roll);
            }
            set {
                LxBits.Set(ref descriptor, L2Coarse.Ap2Mask, L2Coarse.Ap2Roll,
                           (uint)value);
            }
        }

        public AccessPermission AP1
        {
            get {
                return (AccessPermission)
                    LxBits.Get(descriptor, L2Coarse.Ap1Mask, L2Coarse.Ap1Roll);
            }
            set {
                LxBits.Set(ref descriptor, L2Coarse.Ap1Mask, L2Coarse.Ap1Roll,
                           (uint)value);
            }
        }

        public AccessPermission AP0
        {
            get {
                return (AccessPermission)
                    LxBits.Get(descriptor, L2Coarse.Ap0Mask, L2Coarse.Ap0Roll);
            }
            set {
                LxBits.Set(ref descriptor, L2Coarse.Ap0Mask, L2Coarse.Ap0Roll,
                           (uint)value);
            }
        }

        public bool C
        {
            get { return LxBit.Get(this.descriptor, L2Coarse.CBit); }
            set { LxBit.Set(ref this.descriptor, L2Coarse.CBit, value); }
        }

        public bool B
        {
            get { return LxBit.Get(this.descriptor, L2Coarse.BBit); }
            set { LxBit.Set(ref this.descriptor, L2Coarse.BBit, value); }
        }
    }

    ///////////////////////////////////////////////////////////////////////////

    [CLSCompliant(false)]
    public struct L2CoarseSmallEntry
    {
        private uint descriptor;

        public static bool IsType(uint descriptor)
        {
            return IsValid.Get(descriptor, L2Coarse.SmallPageType, 0);
        }

        public void Initialize(uint address)
        {
            this.descriptor = L2Coarse.SmallPageType;
            this.Address    = address;
        }

        public uint Address
        {
            get {
                return LxAddress.Get(descriptor,
                                     L2Coarse.SmallPageAddressMask);
            }
            set {
                LxAddress.Set(ref descriptor,
                              L2Coarse.SmallPageAddressMask,
                              value);
            }
        }

        public AccessPermission AP3
        {
            get {
                return (AccessPermission)
                    LxBits.Get(descriptor, L2Coarse.Ap3Mask, L2Coarse.Ap3Roll);
            }
            set {
                LxBits.Set(ref descriptor, L2Coarse.Ap3Mask, L2Coarse.Ap3Roll,
                           (uint)value);
            }
        }

        public AccessPermission AP2
        {
            get {
                return (AccessPermission)
                    LxBits.Get(descriptor, L2Coarse.Ap2Mask, L2Coarse.Ap2Roll);
            }
            set {
                LxBits.Set(ref descriptor, L2Coarse.Ap2Mask, L2Coarse.Ap2Roll,
                           (uint)value);
            }
        }

        public AccessPermission AP1
        {
            get {
                return (AccessPermission)
                    LxBits.Get(descriptor, L2Coarse.Ap1Mask, L2Coarse.Ap1Roll);
            }
            set {
                LxBits.Set(ref descriptor, L2Coarse.Ap1Mask, L2Coarse.Ap1Roll,
                           (uint)value);
            }
        }

        public AccessPermission AP0
        {
            get {
                return (AccessPermission)
                    LxBits.Get(descriptor, L2Coarse.Ap0Mask, L2Coarse.Ap0Roll);
            }
            set {
                LxBits.Set(ref descriptor, L2Coarse.Ap0Mask, L2Coarse.Ap0Roll,
                           (uint)value);
            }
        }

        public bool C
        {
            get { return LxBit.Get(this.descriptor, L2Coarse.CBit); }
            set { LxBit.Set(ref this.descriptor, L2Coarse.CBit, value); }
        }

        public bool B
        {
            get { return LxBit.Get(this.descriptor, L2Coarse.BBit); }
            set { LxBit.Set(ref this.descriptor, L2Coarse.BBit, value); }
        }

    }

    [CLSCompliant(false)]
    public struct L2CoarseExtendedSmallEntry
    {
        private uint descriptor;

        public static bool IsType(uint descriptor)
        {
            return IsValid.Get(descriptor,
                               L2Coarse.ExtendedSmallPageType,
                               L2Coarse.ExtendedSmallPageSbz);
        }

        public void Initialize(uint address)
        {
            this.descriptor = L2Coarse.ExtendedSmallPageType;
            this.Address    = address;
        }

        public uint Address
        {
            get {
                return LxAddress.Get(descriptor,
                                     L2Coarse.ExtendedSmallPageAddressMask);
            }
            set {
                LxAddress.Set(ref descriptor,
                              L2Coarse.ExtendedSmallPageAddressMask,
                              value);
            }
        }

        public bool S
        {
            get {
                return LxBit.Get(descriptor, L2Coarse.ExtendedSmallPageSBit);
            }
            set {
                LxBit.Set(ref descriptor,
                          L2Coarse.ExtendedSmallPageSBit,
                          value);
            }
        }

        public uint Tex
        {
            get {
                return LxBits.Get(descriptor,
                                  L2Coarse.ExtendedSmallPageTexMask,
                                  L2Coarse.ExtendedSmallPageTexRoll);
            }
            set {
                LxBits.Set(ref descriptor,
                           L2Coarse.ExtendedSmallPageTexMask,
                           L2Coarse.ExtendedSmallPageTexRoll,
                           value);
            }
        }

        public AccessPermission AP
        {
            get {
                return (AccessPermission)
                    LxBits.Get(descriptor, L2Coarse.Ap0Mask, L2Coarse.Ap0Roll);
            }
            set {
                LxBits.Set(ref descriptor, L2Coarse.Ap0Mask, L2Coarse.Ap0Roll,
                           (uint)value);
            }
        }

        public bool C
        {
            get { return LxBit.Get(this.descriptor, L2Coarse.CBit); }
            set { LxBit.Set(ref this.descriptor, L2Coarse.CBit, value); }
        }

        public bool B
        {
            get { return LxBit.Get(this.descriptor, L2Coarse.BBit); }
            set { LxBit.Set(ref this.descriptor, L2Coarse.BBit, value); }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    //
    // Helper routines for common operations that should optimize out
    //

    internal struct IsValid
    {
        internal static bool Get(uint descriptor, uint l1EntryType, uint sbz)
        {
            return (((descriptor & L1.TypeMask) == l1EntryType) &&
                    ((descriptor & sbz) == 0));
        }
    }

    internal struct IsType
    {
        internal static bool Get(uint descriptor, uint entryType)
        {
            return (descriptor & L1.TypeMask) == entryType;
        }
    }

    internal struct LxAddress
    {
        internal static void
        Set(ref uint descriptor, uint addressMask, uint address)
        {
            DebugStub.Assert((address & ~addressMask) == 0);
            descriptor &= ~addressMask;
            descriptor |= address;
        }

        internal static uint Get(uint descriptor, uint addressMask)
        {
            return descriptor & addressMask;
        }
    }

    internal struct LxBit
    {
        internal static void
        Set(ref uint descriptor, uint bitPattern, bool value)
        {
            if (value) {
                descriptor |= bitPattern;
            }
            else {
                descriptor &= bitPattern;
            }
        }

        internal static bool Get(uint descriptor, uint bitPattern)
        {
            return (descriptor & bitPattern) == bitPattern;
        }
    }

    internal struct LxBits
    {
        internal static void
        Set(ref uint descriptor, uint mask, int roll, uint value)
        {
            DebugStub.Assert((mask >> roll) >= value);

            descriptor &= mask;
            descriptor |= value << roll;
        }

        internal static uint
        Get(uint descriptor, uint mask, int roll)
        {
            return (descriptor & mask) >> roll;
        }
    }

    internal struct L1Tex
    {
        internal static void Set(ref uint descriptor, uint tex)
        {
            DebugStub.Assert(IsType.Get(descriptor, L1.SectionType) ||
                             IsType.Get(descriptor, L1.SupersectionType));

            DebugStub.Assert(((tex << L1.TexRoll) & ~L1.TexMask) == 0);

            descriptor = (descriptor & L1.TexMask) | (tex << L1.TexRoll);
        }

        internal static uint Get(uint descriptor)
        {
            DebugStub.Assert(IsType.Get(descriptor, L1.SectionType) ||
                             IsType.Get(descriptor, L1.SupersectionType));

            return (descriptor & L1.TexMask) >> L1.TexRoll;
        }
    }

    internal struct L1AP
    {
        internal static void Set(ref uint descriptor, AccessPermission ap)
        {
            DebugStub.Assert(IsType.Get(descriptor, L1.SectionType) ||
                             IsType.Get(descriptor, L1.SupersectionType));

            descriptor = ((descriptor & ~L1.ApMask) | ((uint)ap) << L1.ApRoll);
        }

        internal static AccessPermission Get(uint descriptor)
        {
            DebugStub.Assert(IsType.Get(descriptor, L1.SectionType) ||
                             IsType.Get(descriptor, L1.SupersectionType));

            return (AccessPermission)((descriptor & L1.ApMask) >> L1.ApRoll);
        }
    }

    internal struct L1Domain
    {

        internal static void Set(ref uint descriptor, uint domain)
        {
            DebugStub.Assert(IsType.Get(descriptor, L1.CoarsePageTableType) ||
                             IsType.Get(descriptor, L1.SectionType) ||
                             IsType.Get(descriptor, L1.FinePageTableType));

            DebugStub.Assert((domain & (L1.DomainMask >> L1.DomainRoll)) == 0);

            descriptor = ((descriptor & ~L1.DomainMask) |
                          (domain << L1.DomainRoll));
        }

        internal static uint Get(uint descriptor)
        {
            DebugStub.Assert(IsType.Get(descriptor, L1.CoarsePageTableType) ||
                             IsType.Get(descriptor, L1.SectionType) ||
                             IsType.Get(descriptor, L1.FinePageTableType));
            return (descriptor & L1.DomainMask) >> L1.DomainRoll;
        }
    }
}

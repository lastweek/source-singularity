///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DriverAttributes.cs
//
//  Warning:  This file is compiled into the kernel, and into the runtime.
//            In order to get the visibility correct in all cases, some #ifs
//            are needed
//
//  New Design:
//          This now conforms with the ideas presented in the Genesis papers,
//          chapter 3.  In particular, a device driver is simply a Category,
//          and anything that is in an app manifest is either intrinsic to
//          apps/installations (and hence not a decoration), or else a
//          PropertySet or Category.

using System;
using Microsoft.Singularity.Configuration;
namespace Microsoft.Singularity.Io
{

    //
    //  The Driver Category
    //

    // Drivers are apps that run in a special Category.  We will designate this
    // by deriving a new class from CategoryDeclaration to represent this
    // special Category, and then creating special field annotations that only
    // apply to this Category.
    //
    public class DriverCategoryDeclaration : CategoryDeclaration
    {

    }

    //////////////////////////////////////////////////////////////////////////
    //
    // DriverCategoryAttribute
    //
    // Purpose: Top-level metadata indicating that an assembly implements the
    //          Driver Category
    //
    // Usage:   Must be applied to a class derived from
    //          DriverCategoryDeclaration
    //
    [AttributeUsage(AttributeTargets.Class, AllowMultiple = false)]
    public class DriverCategoryAttribute : System.Attribute
    {
        public DriverCategoryAttribute()
        {

        }
    }


    //////////////////////////////////////////////////////////////////////////
    //
    // SignatureAttribute
    //
    // Purpose: Declare the signature of the device served by this driver
    //
    // Usage:   Must be applied to a class derived from
    //          DriverCategoryDeclaration
    //
    [AttributeUsage(AttributeTargets.Class, AllowMultiple = true)]
    public class SignatureAttribute : System.Attribute
    {
        // <<deviceIdentifier>> is the prefix of the device signature served by
        // this driver
        private string deviceIdentifier;

        public SignatureAttribute(string deviceIdentifier)
        {
            this.deviceIdentifier = deviceIdentifier;
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // EnumeratesDeviceAttribute
    //
    // Purpose: Declare the signature of a device enumerated by this driver
    //
    // Usage:   Must be applied to a class derived from
    //          DriverCategoryDeclaration
    //
    [AttributeUsage(AttributeTargets.Class, AllowMultiple = true)]
    public class EnumeratesDeviceAttribute : System.Attribute
    {
        // <<deviceIdentifier>> is the prefix of the device signature served by
        // this driver
        private string deviceIdentifier;

        public EnumeratesDeviceAttribute(string deviceIdentifier)
        {
            this.deviceIdentifier = deviceIdentifier;
        }
    }


    //////////////////////////////////////////////////////////////////////////
    //
    // IoRangeAttribute
    //
    // Purpose: All of the Io*RangeAttributes inherit from this one so they
    //          can be processed together using compile-time reflection (CTR).
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    [CLSCompliant(false)]
    public abstract class IoRangeAttribute : System.Attribute
    {
        // <<index>> defaults to -1 (unassigned).  It is the index of the
        // port range in the list of dynamic driver resources.
        private int index;

        internal IoRangeAttribute(int index)
        {
            this.index = index;
            this.shared = false;
        }

        // <<sharable>> defaults to false.  To set it true, use the property
        // Sharable
        private bool shared;
        public bool Shared
        {
            get { return shared; }
            set { shared = value; }
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // IoFixedRangeAttribute
    //
    // Purpose: All of the IoFixed*RangeAttributes inherit from this one so they
    //          can be processed together using compile-time reflection (CTR).
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    [CLSCompliant(false)]
    public abstract class IoFixedRangeAttribute : System.Attribute
    {
        public IoFixedRangeAttribute()
        {
            this.shared = false;
        }

        // <<sharable>> defaults to false.  To set it true, use the property
        // Sharable
        private bool shared;
        public bool Shared
        {
            get { return shared; }
            set { shared = value; }
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // IoPortRangeAttribute
    //
    // Purpose: Decorates a IoPortRange to indicate that the runtime should
    //          preconfigure a PortRange based on the results of PnP
    //          enumeration.  The default is for the IoPortRange to be
    //          read/write.  This can be changed via properties.
    //
    // Usage:   Must decorate an IoPortRange field of a class decorated with
    //          [DriverCategory]
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    [CLSCompliant(false)]
    public class IoPortRangeAttribute : IoRangeAttribute
    {
        // <<baseAddress>> is required.  It is the expected base address of the
        // PortRange
        private uint baseAddress;

        // <<rangeLength>> is required.  It is the expected length of the
        // port range that this driver wants to use.
        private uint rangeLength;

        public IoPortRangeAttribute(int index)
            : base(index)
        {
            this.baseAddress = 0;
            this.rangeLength = 0;
            this.read = true;
            this.write = true;
        }

        public uint Default
        {
            get { return baseAddress; }
            set { baseAddress = value; }
        }

        public uint Length
        {
            get { return rangeLength; }
            set { rangeLength = value; }
        }

        // <<read>> and <<write>> default to true.  To set them false, the
        // Properties AllowRead and AllowWrite can be used
        private bool read;
        public bool AllowRead
        {
            get { return read; }
            set { read = value; }
        }

        private bool write;
        public bool AllowWrite
        {
            get { return write; }
            set { write = value; }
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // IoFixedPortRangeAttribute
    //
    // Purpose: Decorates a IoPortRange to indicate that the runtime should
    //          preconfigure a PortRange based on the these static values.
    //
    // Usage:   Must decorate an IoPortRange field of a class decorated with
    //          [DriverCategory]
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    [CLSCompliant(false)]
    public class IoFixedPortRangeAttribute : IoFixedRangeAttribute
    {
        // <<baseAddress>> is required.  It is the expected base address of the
        // PortRange
        private uint baseAddress;

        // <<rangeLength>> is required.  It is the expected length of the
        // port range that this driver wants to use.
        private uint rangeLength;

        public IoFixedPortRangeAttribute()
        {
            this.baseAddress = baseAddress;
            this.rangeLength = rangeLength;
            this.read = true;
            this.write = true;
        }

        public uint Base
        {
            get { return baseAddress; }
            set { baseAddress = value; }
        }

        public uint Length
        {
            get { return rangeLength; }
            set { rangeLength = value; }
        }

        // <<read>> and <<write>> default to true.  To set them false, the
        // Properties AllowRead and AllowWrite can be used
        private bool read;
        public bool AllowRead
        {
            get { return read; }
            set { read = value; }
        }

        private bool write;
        public bool AllowWrite
        {
            get { return write; }
            set { write = value; }
        }

    }

    //////////////////////////////////////////////////////////////////////////
    //
    // IoIrqRangeAttribute
    //
    // Purpose: Decorates an IoIrqRange object to indicate that the runtime
    //          should preconfigure an IrqRange based on the results of Pnp.
    //
    // Usage:   Must decorate an IoIrqRange field of a class decorated with
    //          [DriverCategory]
    //
    //[TODO] should these really be byte, or should they be ushort?
    [CLSCompliant(false)]
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public class IoIrqRangeAttribute : IoRangeAttribute
    {
        // <<defaultBase>> is the default Irq for the device.  It is a required
        // parameter to the constructor.
        private byte baseAddress;

        // <<defaultLength>> is the default length of the Irq range.  It is also
        // a required parameter
        private byte rangeLength;

        public IoIrqRangeAttribute(int index)
            : base(index)
        {
            this.baseAddress = 0;
            this.rangeLength = 1;
        }

        public byte Default
        {
            get { return baseAddress; }
            set { baseAddress = value; }
        }

        public byte Length
        {
            get { return rangeLength; }
            set { rangeLength = value; }
        }
    }


    //////////////////////////////////////////////////////////////////////////
    //
    // IoIrqRangeAttribute
    //
    // Purpose: Decorates an IoIrqRange object to indicate that the runtime
    //          should preconfigure an IrqRange based on the results of Pnp.
    //
    // Usage:   Must decorate an IoIrqRange field of a class decorated with
    //          [DriverCategory]
    //
    //[TODO] should these really be byte, or should they be ushort?
    [CLSCompliant(false)]
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public class IoFixedIrqRangeAttribute : IoFixedRangeAttribute
    {
        // <<defaultBase>> is the default Irq for the device.  It is a required
        // parameter to the constructor.
        private byte baseAddress;

        // <<defaultLength>> is the default length of the Irq range.  It is also
        // a required parameter
        private byte rangeLength;

        public IoFixedIrqRangeAttribute()
            : base()
        {
            this.baseAddress = 0;
            this.rangeLength = 1;
        }

        public byte Base
        {
            get { return baseAddress; }
            set { baseAddress = value; }
        }

        public byte Length
        {
            get { return rangeLength; }
            set { rangeLength = value; }
        }
    }


    //////////////////////////////////////////////////////////////////////////
    //
    // IoDmaRangeAttribute
    //
    // Purpose: Decorates an IoDma object to indicate that the runtime should
    //          preconfigure a Dma channel based on the results of Pnp.
    //
    // Usage:   Must decorate an IoDmaRange field of a class decorated with
    //          [DriverCategory]
    //
    [CLSCompliant(false)]
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    public class IoDmaRangeAttribute : IoRangeAttribute
    {
        // <<defaultBase>> is the default Dma for the device
        private byte baseAddress;

        // <<defaultLength>> is the default length of the Dma range
        private byte rangeLength;

        public IoDmaRangeAttribute(int index)
            : base(index)
        {
            this.baseAddress = 0;
            this.rangeLength = 1;
        }

        public byte Default
        {
            get { return baseAddress; }
            set { baseAddress = value; }
        }

        public byte Length
        {
            get { return rangeLength; }
            set { rangeLength = value; }
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // IoMemoryRangeAttribute
    //
    // Purpose: Decorates an IoMemory object to indicate that the runtime should
    //          preconfigure some memory based on the results of Pnp.  The
    //          memory region is assumed to be read/write, unless these
    //          values are changed via properties.
    //
    // Usage:   Must decorate an IoMemoryRange field of a class decorated with
    //          [DriverCategory]
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    [CLSCompliant(false)]
    public class IoMemoryRangeAttribute : IoRangeAttribute
    {
        // <<defaultBase>> is required.  It is the expected base address of this
        // memory range.  Use 0 if unsure.
        private uint baseAddress;

        // <<defaultSize>> is required.  It is the minimum acceptable size of
        // the region.
        private uint rangeLength;

        // <<read>> and <<write>> default to true.  To set them false, use the
        // Properties AllowRead and AllowWrite
        private bool read;
        private bool write;

        public IoMemoryRangeAttribute(int index)
            : base(index)
        {
            this.baseAddress = baseAddress;
            this.rangeLength = rangeLength;
            this.read = true;
            this.write = true;
        }

        public bool AllowRead
        {
            get { return read; }
            set { read = value; }
        }

        public bool AllowWrite
        {
            get { return write; }
            set { write = value; }
        }

        public uint Default
        {
            get { return baseAddress; }
            set { baseAddress = value; }
        }

        public uint Length
        {
            get { return rangeLength; }
            set { rangeLength = value; }
        }
    }

    //////////////////////////////////////////////////////////////////////////
    //
    // IoMemoryRangeAttribute
    //
    // Purpose: Decorates an IoMemory object to indicate that the runtime should
    //          preconfigure are static memory region.  The
    //          memory region is assumed to be read/write, unless these
    //          values are changed via properties.
    //
    // Usage:   Must decorate an IoMemoryRange field of a class decorated with
    //          [DriverCategory]
    //
    [AttributeUsage(AttributeTargets.Field, AllowMultiple = false)]
    [CLSCompliant(false)]
    public class IoFixedMemoryRangeAttribute : IoFixedRangeAttribute
    {
        // <<baseAddress>> defaults to 0, any base.  It is the expected base
        // address of this memory range.
        private uint baseAddress;

        // <<alignment>> defaults to 0.  It is the expected alignment.
        private uint alignment;

        // <<defaultSize>> is required.  It is the minimum acceptable size of
        // the region.
        private uint rangeLength;

        // <<addressBits>> defaults to 32.  It is the # of address bits
        // supported by the hardware.  Used to mark memory that must fit in
        // low 24 bits for legacy ISA devices, or low 32 bits for legacy PCI
        // devices.
        private int addressBits;

        // <<read>> and <<write>> default to true.  To set them false, use the
        // Properties AllowRead and AllowWrite
        private bool read;
        private bool write;

        public IoFixedMemoryRangeAttribute()
        {
            this.addressBits = 32;
            this.alignment = 0;
            this.baseAddress = 0;
            this.rangeLength = 0;
            this.read = true;
            this.write = true;
        }

        public int AddressBits
        {
            get { return addressBits; }
            set { addressBits = value; }
        }

        public uint Alignment
        {
            get { return alignment; }
            set { alignment = value; }
        }

        public bool AllowRead
        {
            get { return read; }
            set { read = value; }
        }

        public bool AllowWrite
        {
            get { return write; }
            set { write = value; }
        }

        public uint Base
        {
            get { return baseAddress; }
            set { baseAddress = value; }
        }

        public uint Length
        {
            get { return rangeLength; }
            set { rangeLength = value; }
        }
    }
}
